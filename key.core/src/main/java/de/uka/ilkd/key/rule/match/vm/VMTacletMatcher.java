/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;
import de.uka.ilkd.key.rule.match.TacletMatcherKit;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchSchemaVariableInstruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.*;
import org.key_project.prover.rules.conditions.NotFreeIn;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.AssumesMatchResult;
import org.key_project.prover.rules.instantiation.MatchConditions;
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
    private final TacletMatchProgram findMatchProgram;
    /** the matcher for the taclet's assumes formulas */
    private final HashMap<Term, TacletMatchProgram> assumesMatchPrograms = new HashMap<>();

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
    private final ImmutableSet<org.key_project.logic.op.QuantifiableVariable> boundVars;

    /**
     * flag indicating if preceding updates of the term to be matched should be ignored this
     * requires the taclet to ignore updates and that the find term does not start with an
     * {@link UpdateApplication} operator
     */
    private final boolean ignoreTopLevelUpdates;
    /**
     * the find expression of the taclet of {@code null} if it is a {@link NoFindTaclet}
     */
    private final Term findExp;

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
            ignoreTopLevelUpdates = ((FindTaclet) taclet).ignoreTopLevelUpdates()
                    && !(findExp.op() instanceof UpdateApplication);
            findMatchProgram = TacletMatchProgram.createProgram(findExp);

        } else {
            ignoreTopLevelUpdates = false;
            findExp = null;
            findMatchProgram = TacletMatchProgram.EMPTY_PROGRAM;
        }

        for (SequentFormula sf : assumesSequent) {
            assumesMatchPrograms.put((Term) sf.formula(),
                TacletMatchProgram.createProgram((Term) sf.formula()));
        }
    }


    /**
     * (non-Javadoc)
     *
     * @see TacletMatcher#matchAssumes(Iterable, org.key_project.logic.Term, MatchConditions,
     *      LogicServices)
     */
    @Override
    public final AssumesMatchResult matchAssumes(Iterable<AssumesFormulaInstantiation> p_toMatch,
            org.key_project.logic.Term p_template,
            org.key_project.prover.rules.instantiation.MatchConditions p_matchCond,
            LogicServices p_services) {
        TacletMatchProgram prg = assumesMatchPrograms.get(p_template);
        final var mc = (de.uka.ilkd.key.rule.MatchConditions) p_matchCond;

        ImmutableList<AssumesFormulaInstantiation> resFormulas = ImmutableSLList.nil();
        ImmutableList<MatchConditions> resMC =
            ImmutableSLList.nil();

        final boolean updateContextPresent = !mc.getInstantiations().getUpdateContext().isEmpty();
        ImmutableList<UpdateLabelPair> context = ImmutableSLList.nil();

        if (updateContextPresent) {
            context = mc.getInstantiations().getUpdateContext();
        }

        for (var cf : p_toMatch) {
            Term formula = (Term) cf.getSequentFormula().formula();

            if (updateContextPresent) {
                formula = matchUpdateContext(context, formula);
            }
            if (formula != null) {// update context not present or update context match succeeded
                final MatchConditions newMC =
                    checkConditions(prg.match(formula, mc, p_services), p_services);

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
    private Term matchUpdateContext(ImmutableList<UpdateLabelPair> context, Term formula) {
        ImmutableList<UpdateLabelPair> curContext = context;
        for (int i = 0, size = context.size(); i < size; i++) {
            if (formula.op() instanceof UpdateApplication) {
                final Term update = UpdateApplication.getUpdate(formula);
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
     * @see TacletMatcher#matchAssumes(Iterable, MatchConditions, LogicServices)
     */
    @Override
    public final MatchConditions matchAssumes(
            Iterable<AssumesFormulaInstantiation> p_toMatch,
            MatchConditions p_matchCond,
            LogicServices p_services) {

        final Iterator<SequentFormula> anteIterator = assumesSequent.antecedent().iterator();
        final Iterator<SequentFormula> succIterator = assumesSequent.succedent().iterator();

        ImmutableList<MatchConditions> newMC;

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
    public final MatchConditions checkConditions(
            org.key_project.prover.rules.instantiation.MatchConditions cond,
            LogicServices services) {
        var result = (de.uka.ilkd.key.rule.MatchConditions) cond;
        if (result != null) {

            final var svIterator = result.getInstantiations().svIterator();

            if (!svIterator.hasNext()) {
                return checkVariableConditions(null, null, cond, services);// XXX
            }

            while (result != null && svIterator.hasNext()) {
                final SchemaVariable sv = svIterator.next();
                final Object o = result.getInstantiations().getInstantiation(sv);
                if (o instanceof SyntaxElement se) {
                    result = (de.uka.ilkd.key.rule.MatchConditions) checkVariableConditions(sv, se,
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
    public final MatchConditions checkVariableConditions(SchemaVariable var,
            SyntaxElement instantiationCandidate,
            org.key_project.prover.rules.instantiation.MatchConditions matchCond,
            LogicServices services) {
        if (matchCond != null) {
            if (instantiationCandidate instanceof Term term) {
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
    private Pair<Term, MatchConditions> matchAndIgnoreUpdatePrefix(
            final Term source,
            final MatchConditions matchCond) {
        final Operator sourceOp = source.op();

        if (sourceOp instanceof UpdateApplication) {
            // updates can be ignored
            Term update = UpdateApplication.getUpdate(source);
            final var svInstantiations =
                ((de.uka.ilkd.key.rule.MatchConditions) matchCond).getInstantiations();
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
    public final MatchConditions matchFind(
            org.key_project.logic.Term term,
            MatchConditions p_matchCond,
            LogicServices services) {
        if (findMatchProgram == TacletMatchProgram.EMPTY_PROGRAM) {
            return null;
        }
        Term source = (Term) term;
        if (ignoreTopLevelUpdates) {
            Pair</* term below updates */Term, MatchConditions> resultUpdateMatch =
                matchAndIgnoreUpdatePrefix(source, p_matchCond);
            source = resultUpdateMatch.first;
            p_matchCond = resultUpdateMatch.second;
        }
        return checkConditions(
            findMatchProgram.match(source, (de.uka.ilkd.key.rule.MatchConditions) p_matchCond,
                services),
            services);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions matchSV(SchemaVariable sv,
            SyntaxElement syntaxElement,
            org.key_project.prover.rules.instantiation.MatchConditions matchCond,
            LogicServices services) {

        final MatchSchemaVariableInstruction<? extends SchemaVariable> instr =
            TacletMatchProgram.getMatchInstructionForSV(sv);

        if (syntaxElement instanceof Term term) {
            matchCond =
                instr.match(term, (de.uka.ilkd.key.rule.MatchConditions) matchCond, services);
            matchCond = checkVariableConditions(sv, syntaxElement, matchCond, services);
        } else if (syntaxElement instanceof ProgramElement pe) {
            matchCond = instr.match(pe, (de.uka.ilkd.key.rule.MatchConditions) matchCond, services);
            matchCond = checkConditions(matchCond, services);
        }
        return matchCond;
    }

}
