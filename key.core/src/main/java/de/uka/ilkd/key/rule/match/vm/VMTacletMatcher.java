/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;
import de.uka.ilkd.key.rule.match.TacletMatcherKit;
import de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchSchemaVariableInstruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.*;
import org.key_project.prover.rules.conditions.NotFreeIn;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.AssumesMatchResult;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * <p>
 * Matching algorithm using a virtual machine based approach inspired by Voronkonv et al. It matches
 * exactly one taclet and does not produce code trees.
 * </p>
 * <p>
 * Instances of this class should <strong>not</strong> be created directly, use
 * {@link TacletMatcherKit#createTacletMatcher(Taclet)} instead.
 * </p>
 *
 * @see TacletMatcherKit
 */
public class VMTacletMatcher implements TacletMatcher {

    /** the matcher for the find expression of the taclet */
    private final VMProgramInterpreter findMatchProgram;
    /** the matcher for the taclet's assumes formulas */
    private final HashMap<JTerm, VMProgramInterpreter> assumesMatchPrograms = new HashMap<>();

    /**
     * the variable conditions of the taclet that need to be satisfied by found schema variable
     * instantiations
     */
    private final ImmutableList<? extends VariableCondition> varconditions;
    /** the built-in notFreeIn variable conditions */
    private final ImmutableList<? extends NotFreeIn> varsNotFreeIn;

    /** the assumes sequent of the taclet */
    private final Sequent assumesSequent;
    /** the bound variables */
    private final ImmutableSet<QuantifiableVariable> boundVars;

    /**
     * flag indicating if preceding updates of the term to be matched should be ignored this
     * requires the taclet to ignore updates and that the find term does not start with an
     * {@link UpdateApplication} operator
     */
    private final boolean ignoreTopLevelUpdates;
    /**
     * the find expression of the taclet of {@code null} if it is a {@link NoFindTaclet}
     */
    private final JTerm findExp;

    /**
     * @param taclet the Taclet matched by this matcher
     */
    public VMTacletMatcher(Taclet taclet) {
        varconditions = taclet.getVariableConditions();
        assumesSequent = taclet.assumesSequent();
        boundVars = taclet.getBoundVariables();
        varsNotFreeIn = taclet.varsNotFreeIn();

        if (taclet instanceof FindTaclet) {
            findExp = ((FindTaclet) taclet).find();
            ignoreTopLevelUpdates = taclet.ignoreTopLevelUpdates()
                    && !(findExp.op() instanceof UpdateApplication);
            findMatchProgram =
                new VMProgramInterpreter(SyntaxElementMatchProgramGenerator.createProgram(findExp));

        } else {
            ignoreTopLevelUpdates = false;
            findExp = null;
            findMatchProgram = null;
        }

        for (SequentFormula sf : assumesSequent) {
            assumesMatchPrograms.put((JTerm) sf.formula(),
                new VMProgramInterpreter(
                    SyntaxElementMatchProgramGenerator.createProgram((JTerm) sf.formula())));
        }
    }

    /**
     * (non-Javadoc)
     *
     * @see TacletMatcher#matchAssumes(Iterable, org.key_project.logic.Term, MatchResultInfo,
     *      LogicServices)
     */
    @Override
    public final AssumesMatchResult matchAssumes(Iterable<AssumesFormulaInstantiation> p_toMatch,
            Term p_template,
            MatchResultInfo p_matchCond,
            LogicServices p_services) {
        VMProgramInterpreter interpreter = assumesMatchPrograms.get(p_template);
        final var mc = (MatchConditions) p_matchCond;

        ImmutableList<AssumesFormulaInstantiation> resFormulas = ImmutableSLList.nil();
        ImmutableList<MatchResultInfo> resMC =
            ImmutableSLList.nil();

        final boolean updateContextPresent = !mc.getInstantiations().getUpdateContext().isEmpty();
        ImmutableList<UpdateLabelPair> context = ImmutableSLList.nil();

        if (updateContextPresent) {
            context = mc.getInstantiations().getUpdateContext();
        }

        for (var cf : p_toMatch) {
            JTerm formula = (JTerm) cf.getSequentFormula().formula();

            if (updateContextPresent) {
                formula = matchUpdateContext(context, formula);
            }
            if (formula != null) {// update context not present or update context match succeeded
                final MatchResultInfo newMC =
                    checkConditions(interpreter.match(formula, mc, p_services), p_services);

                if (newMC != null) {
                    resFormulas = resFormulas.prepend(cf);
                    resMC = resMC.prepend(newMC);
                }
            }
        }
        return new AssumesMatchResult(resFormulas, resMC);
    }

    /**
     * the formula ensures that the update context described the update of the given formula.
     * If it does not then {@code null} is returned, otherwise the formula without the update
     * context.
     *
     * @param context the list of update label pairs describing the update context
     * @param formula the formula whose own update context must be equal (modulo renaming) to the
     *        given one
     * @return {@code null} if the update context does not match the one of the formula or the
     *         formula without the update context
     */
    private JTerm matchUpdateContext(ImmutableList<UpdateLabelPair> context, JTerm formula) {
        ImmutableList<UpdateLabelPair> curContext = context;
        for (int i = 0, size = context.size(); i < size; i++) {
            if (formula.op() instanceof UpdateApplication) {
                final JTerm update = UpdateApplication.getUpdate(formula);
                final UpdateLabelPair ulp = curContext.head();
                if (RENAMING_TERM_PROPERTY.equalsModThisProperty(ulp.update(), update)
                        && ulp.updateApplicationlabels().equals(update.getLabels())) {
                    curContext = curContext.tail();
                    formula = UpdateApplication.getTarget(formula);
                    continue;
                }
            }
            // update context does not match update prefix of formula
            return null;
        }
        return formula;
    }


    /**
     * @see TacletMatcher#matchAssumes(Iterable, MatchResultInfo, LogicServices)
     */
    @Override
    public final MatchResultInfo matchAssumes(
            Iterable<AssumesFormulaInstantiation> p_toMatch,
            MatchResultInfo p_matchCond,
            LogicServices p_services) {

        final Iterator<SequentFormula> anteIterator = assumesSequent.antecedent().iterator();
        final Iterator<SequentFormula> succIterator = assumesSequent.succedent().iterator();

        ImmutableList<MatchResultInfo> newMC;

        for (final AssumesFormulaInstantiation candidateInst : p_toMatch) {
            // Part of fix for #1716: match antecedent with antecedent, succ with succ
            boolean candidateInAntec =
                (candidateInst instanceof AssumesFormulaInstSeq candidateInSeq)
                        // Only IfFormulaInstSeq has inAntec() property ...
                        && (candidateInSeq.inAntecedent())
                        || !(candidateInst instanceof AssumesFormulaInstSeq)
                                // ... and it seems we don't need the check for other
                                // implementations.
                                // Default: just take the next ante formula, else succ formula
                                && anteIterator.hasNext();

            final var assumesSequentIterator = candidateInAntec ? anteIterator : succIterator;
            // Fix end

            assert assumesSequentIterator.hasNext()
                    : "p_toMatch and assumes sequent must have same number of elements";
            newMC = matchAssumes(
                ImmutableSLList.<AssumesFormulaInstantiation>nil().prepend(candidateInst),
                assumesSequentIterator.next().formula(), p_matchCond, p_services).matchConditions();

            if (newMC.isEmpty()) {
                return null;
            }

            p_matchCond = newMC.head();
        }
        assert !anteIterator.hasNext() && !succIterator.hasNext()
                : "p_toMatch and assumes sequent must have same number of elements";

        return p_matchCond;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchResultInfo checkConditions(
            MatchResultInfo cond,
            LogicServices services) {
        var result = (MatchConditions) cond;
        if (result != null) {

            final var svIterator = result.getInstantiations().svIterator();

            if (!svIterator.hasNext()) {
                return checkVariableConditions(null, null, cond, services);// XXX
            }

            while (result != null && svIterator.hasNext()) {
                final SchemaVariable sv = svIterator.next();
                final Object o = result.getInstantiations().getInstantiation(sv);
                if (o instanceof SyntaxElement se) {
                    result = (MatchConditions) checkVariableConditions(sv, se,
                        result, services);
                }
            }
        }

        return result;
    }

    /**
     * looks if a variable is declared as not free in
     *
     * @param var the SchemaVariable to look for
     * @return true iff declared not free
     */
    private boolean varDeclaredNotFree(SchemaVariable var) {
        for (final NotFreeIn nfi : varsNotFreeIn) {
            if (nfi.first() == var) {
                return true;
            }
        }
        return false;
    }


    /**
     * returns true iff the given variable is bound either in the ifSequent or in any part of the
     * TacletGoalTemplates
     *
     * @param v the bound variable to be searched
     */
    private boolean varIsBound(SchemaVariable v) {
        return (v instanceof QuantifiableVariable) && boundVars.contains(v);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchResultInfo checkVariableConditions(SchemaVariable var,
            SyntaxElement instantiationCandidate,
            MatchResultInfo matchCond,
            LogicServices services) {
        if (matchCond != null) {
            if (instantiationCandidate instanceof JTerm term) {
                if (!(term.op() instanceof QuantifiableVariable)) {
                    if (varIsBound(var) || varDeclaredNotFree(var)) {
                        // match(x) is not a variable, but the corresponding template variable is
                        // bound
                        // or declared non free (so it has to be matched to a variable)
                        return null; // FAILED
                    }
                }
            }
            // check generic conditions
            for (final VariableCondition vc : varconditions) {
                matchCond = vc.check(var, instantiationCandidate, matchCond, services);
                if (matchCond == null) {
                    return null; // FAILED
                }
            }
        }
        return matchCond;
    }

    /**
     * ignores a possible update prefix This method assumes that the taclet allows to ignore updates
     * and the find expression does not start with an update application operator
     *
     * @param source the term to be matched
     * @param matchCond the accumulated match conditions for a successful match
     * @return a pair of updated match conditions and the unwrapped term without the ignored updates
     *         (Which have been added to the update context in the match conditions)
     */
    private Pair<JTerm, MatchResultInfo> matchAndIgnoreUpdatePrefix(
            final JTerm source,
            final MatchResultInfo matchCond) {
        final Operator sourceOp = source.op();

        if (sourceOp instanceof UpdateApplication) {
            // updates can be ignored
            JTerm update = UpdateApplication.getUpdate(source);
            final var svInstantiations =
                ((MatchConditions) matchCond).getInstantiations();
            final var resultingConditions =
                matchCond.setInstantiations(svInstantiations.addUpdate(update, source.getLabels()));
            return matchAndIgnoreUpdatePrefix(UpdateApplication.getTarget(source),
                resultingConditions);
        } else {
            return new Pair<>(source, matchCond);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchResultInfo matchFind(
            Term term,
            MatchResultInfo p_matchCond,
            LogicServices services) {
        if (findMatchProgram == null) {
            return null;
        }
        JTerm source = (JTerm) term;
        if (ignoreTopLevelUpdates) {
            Pair</* term below updates */JTerm, MatchResultInfo> resultUpdateMatch =
                matchAndIgnoreUpdatePrefix(source, p_matchCond);
            source = resultUpdateMatch.first;
            p_matchCond = resultUpdateMatch.second;
        }
        return checkConditions(
            findMatchProgram.match(source, p_matchCond, services),
            services);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public MatchResultInfo matchSV(SchemaVariable sv,
            SyntaxElement syntaxElement,
            MatchResultInfo matchCond,
            LogicServices services) {

        final MatchSchemaVariableInstruction instr =
            JavaDLMatchVMInstructionSet.getMatchInstructionForSV(sv);

        if (syntaxElement instanceof JTerm term) {
            matchCond = instr.match(term, matchCond, services);
            matchCond = checkVariableConditions(sv, syntaxElement, matchCond, services);
        } else if (syntaxElement instanceof ProgramElement pe) {
            matchCond = instr.match(pe, (MatchConditions) matchCond, services);
            matchCond = checkConditions(matchCond, services);
        }
        return matchCond;
    }

}
