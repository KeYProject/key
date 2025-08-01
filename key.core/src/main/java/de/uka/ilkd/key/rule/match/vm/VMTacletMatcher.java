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

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

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
    private final HashMap<Term, @NonNull VMProgramInterpreter> assumesMatchPrograms =
        new HashMap<>();

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

        if (taclet instanceof final FindTaclet findTaclet) {
            findExp = findTaclet.find();
            ignoreTopLevelUpdates = taclet.ignoreTopLevelUpdates()
                    && !(findExp.op() instanceof UpdateApplication);
            findMatchProgram =
                new VMProgramInterpreter(SyntaxElementMatchProgramGenerator.createProgram(findExp));

        } else {
            ignoreTopLevelUpdates = false;
            findExp = null;
            findMatchProgram = null;
        }

        for (final SequentFormula sf : assumesSequent) {
            assumesMatchPrograms.put(sf.formula(),
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
    public final @NonNull AssumesMatchResult matchAssumes(
            @NonNull Iterable<@NonNull AssumesFormulaInstantiation> p_toMatch,
            @NonNull Term p_template,
            @NonNull MatchResultInfo p_matchCond,
            @NonNull LogicServices p_services) {
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
    public final @Nullable MatchResultInfo matchAssumes(
            @NonNull Iterable<AssumesFormulaInstantiation> p_toMatch,
            @NonNull MatchResultInfo p_matchCond,
            @NonNull LogicServices p_services) {

        final Iterator<SequentFormula> anteIterator = assumesSequent.antecedent().iterator();
        final Iterator<SequentFormula> succIterator = assumesSequent.succedent().iterator();

        ImmutableList<MatchResultInfo> newMC;

        for (final AssumesFormulaInstantiation candidateInst : p_toMatch) {
            // Part of fix for #1716: match antecedent with antecedent, succ with succ
            boolean candidateInAntec =
                (candidateInst instanceof final AssumesFormulaInstSeq candidateInSeq)
                        // Only if AssumesFormulaInstSeq has inAntec() property ...
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
    public final @Nullable MatchResultInfo checkConditions(
            @Nullable MatchResultInfo cond,
            @NonNull LogicServices services) {
        var result = (MatchConditions) cond;
        if (result != null) {

            final var svIterator = result.getInstantiations().svIterator();

            if (!svIterator.hasNext()) {
                // for example SimplifyIfThenElseUpdateCondition
                // rewrite these conditions and avoid null; conditions that do not involve matched
                // variables
                return checkVariableConditions(null, null, cond, services);// XXX
            }

            while (result != null && svIterator.hasNext()) {
                final SchemaVariable sv = svIterator.next();
                final Object o = result.getInstantiations().getInstantiation(sv);
                if (o instanceof SyntaxElement se) {
                    result = (MatchConditions) checkVariableConditions(sv, se, result, services);
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
    public final @Nullable MatchResultInfo checkVariableConditions(@Nullable SchemaVariable var,
            @Nullable SyntaxElement instantiationCandidate,
            @Nullable MatchResultInfo matchCond,
            @NonNull LogicServices services) {
        if (matchCond != null) {
            if (instantiationCandidate instanceof JTerm term) {
                if (!(term.op() instanceof QuantifiableVariable)) {
                    if (varIsBound(var) || varDeclaredNotFree(var)) {
                        // match(x) is not a variable, but the corresponding template variable is
                        // bound or declared non free (so it has to be matched to a variable)
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
     * @param matchResult the accumulated match conditions for a successful match
     * @return a pair of updated match conditions and the unwrapped term without the ignored updates
     *         (Which have been added to the update context in the match conditions)
     */
    private Pair<JTerm, MatchResultInfo> matchAndIgnoreUpdatePrefix(
            JTerm source, final MatchResultInfo matchResult) {
        final MatchConditions matchCond = (MatchConditions) matchResult;
        final var instantiations = matchCond.getInstantiations();
        ImmutableList<UpdateLabelPair> updateLabel = instantiations.getUpdateContext();
        while (source.op() instanceof UpdateApplication) {
            final JTerm update = UpdateApplication.getUpdate(source);
            updateLabel = updateLabel.append(new UpdateLabelPair(update, source.getLabels()));
            source = UpdateApplication.getTarget(source);
        }
        return new Pair<>(source,
            matchCond.setInstantiations(instantiations.addUpdateList(updateLabel)));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final @Nullable MatchResultInfo matchFind(
            @NonNull Term term,
            @NonNull MatchResultInfo p_matchCond,
            @NonNull LogicServices services) {
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
        final MatchResultInfo matchResult = findMatchProgram.match(source, p_matchCond, services);
        return matchResult == null ? null : checkConditions(matchResult, services);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchResultInfo matchSV(@NonNull SchemaVariable sv,
            @NonNull SyntaxElement syntaxElement,
            @NonNull MatchResultInfo matchCond,
            @NonNull LogicServices services) {

        final MatchSchemaVariableInstruction instr =
            JavaDLMatchVMInstructionSet.getMatchInstructionForSV(sv);

        matchCond = instr.match(syntaxElement, matchCond, services);
        if (syntaxElement instanceof JTerm) {
            matchCond = checkVariableConditions(sv, syntaxElement, matchCond, services);
        } else if (syntaxElement instanceof ProgramElement) {
            matchCond = checkConditions(matchCond, services);
        }
        return matchCond;
    }

}
