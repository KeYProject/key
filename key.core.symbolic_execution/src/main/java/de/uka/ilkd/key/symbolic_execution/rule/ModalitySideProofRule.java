/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * A {@link BuiltInRule} which evaluates a modality in a side proof.
 * </p>
 * <p>
 * This rule is applicable on top level terms ({@link SequentFormula}) of the form.
 * <ul>
 * <li>{@code {...}\[...\](<something> = <var>)} or</li>
 * <li>{@code {...}\<...\>(<something> = <var>)} or</li>
 * <li>{@code {...}\[...\](<var> = <something>)} or</li>
 * <li>{@code {...}\<...\>(<var> = <something>)}</li>
 * </ul>
 * The leading updates are optional and any {@link JModality} is supported.
 * </p>
 * <p>
 * The original {@link SequentFormula} which contains the equality is always removed in the
 * following {@link Goal}. For each possible result value is a {@link SequentFormula} added to the
 * {@link Sequent} of the form:
 * <ul>
 * <li>Antecedent: {@code <resultCondition> -> <something> = <result>} or</li>
 * <li>Antecedent: {@code <resultCondition> -> <result> = <something>} or</li>
 * <li>Succedent: {@code <resultCondition> & <something> = <result>} or</li>
 * <li>Succedent: {@code <resultCondition> & <result> = <something>}</li>
 * </ul>
 * The side proof uses the default side proof settings (splitting = delayed) and is started via
 * {@link SymbolicExecutionSideProofUtil#startSideProof}. In
 * case that at least one result branch has applicable rules an exception is thrown and the rule is
 * aborted.
 * </p>
 *
 * @author Martin Hentschel
 */
public class ModalitySideProofRule extends AbstractSideProofRule {
    /**
     * The singleton instance of this class.
     */
    public static final ModalitySideProofRule INSTANCE = new ModalitySideProofRule();

    /**
     * The {@link Name} of this rule.
     */
    private static final Name NAME = new Name("Evaluate Modality in Side Proof");

    /**
     * Constructor to forbid multiple instances.
     */
    private ModalitySideProofRule() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        boolean applicable = false;
        if (pio != null && pio.isTopLevel()) {
            // abort if inside of transformer
            if (Transformer.inTransformer(pio)) {
                return false;
            }
            JTerm term = TermBuilder.goBelowUpdates((JTerm) pio.subTerm());
            if (term.op() instanceof JModality
                    && SymbolicExecutionUtil.getSymbolicExecutionLabel(term) == null) {
                JTerm equalityTerm = term.sub(0);
                if (equalityTerm.op() == Junctor.IMP) {
                    equalityTerm = equalityTerm.sub(0);
                }
                if (equalityTerm.op() == Junctor.NOT) {
                    equalityTerm = equalityTerm.sub(0);
                }
                if (equalityTerm.op() == Equality.EQUALS) {
                    if (equalityTerm.sub(0).op() instanceof IProgramVariable
                            || equalityTerm.sub(1).op() instanceof IProgramVariable) {

                        applicable = true;
                    }
                }
            }
        }
        return applicable;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp)
            throws RuleAbortException {
        try {
            // Extract required Terms from goal
            PosInOccurrence pio = ruleApp.posInOccurrence();
            JTerm topLevelTerm = (JTerm) pio.subTerm();
            Pair<ImmutableList<JTerm>, JTerm> updatesAndTerm =
                TermBuilder.goBelowUpdates2(topLevelTerm);
            JTerm modalityTerm = updatesAndTerm.second;
            ImmutableList<JTerm> updates = updatesAndTerm.first;
            boolean inImplication = false;
            JTerm equalityTerm = modalityTerm.sub(0);
            if (equalityTerm.op() == Junctor.IMP) {
                inImplication = true;
                equalityTerm = equalityTerm.sub(0);
            }
            boolean negation = false;
            if (equalityTerm.op() == Junctor.NOT) {
                negation = true;
                equalityTerm = equalityTerm.sub(0);
            }
            JTerm otherTerm;
            JTerm varTerm;
            boolean varFirst;
            if (equalityTerm.sub(0).op() instanceof LocationVariable) {
                otherTerm = equalityTerm.sub(1);
                varTerm = equalityTerm.sub(0);
                varFirst = true;
            } else {
                otherTerm = equalityTerm.sub(0);
                varTerm = equalityTerm.sub(1);
                varFirst = false;
            }
            // Compute sequent for side proof to compute query in.
            // New OneStepSimplifier is required because it has an internal state and the default
            // instance can't be used parallel.
            final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil
                    .cloneProofEnvironmentWithOwnOneStepSimplifier(goal.proof(), true);
            final Services sideProofServices = sideProofEnv.getServicesForEnvironment();
            Sequent sequentToProve = SymbolicExecutionSideProofUtil
                    .computeGeneralSequentToProve(goal.sequent(),
                        pio.sequentFormula());
            Function newPredicate = createResultFunction(sideProofServices, varTerm.sort());
            final TermBuilder tb = sideProofServices.getTermBuilder();
            JTerm newTerm = tb.func(newPredicate, varTerm);
            JTerm newModalityTerm = sideProofServices.getTermFactory().createTerm(modalityTerm.op(),
                new ImmutableArray<>(newTerm), modalityTerm.boundVars(),
                modalityTerm.getLabels());
            JTerm newModalityWithUpdatesTerm = tb.applySequential(updates, newModalityTerm);
            sequentToProve = sequentToProve
                    .addFormula(new SequentFormula(newModalityWithUpdatesTerm), false, false)
                    .sequent();
            // Compute results and their conditions
            List<ResultsAndCondition> conditionsAndResultsMap =
                computeResultsAndConditions(goal, sideProofEnv, sequentToProve,
                    newPredicate);
            // Create new single goal in which the query is replaced by the possible results
            ImmutableList<Goal> goals = goal.split(1);
            Goal resultGoal = goals.head();
            resultGoal.removeFormula(pio);
            // Create results
            Set<JTerm> resultTerms = new LinkedHashSet<>();
            for (ResultsAndCondition conditionsAndResult : conditionsAndResultsMap) {
                JTerm conditionTerm = tb.and(conditionsAndResult.conditions());
                JTerm resultEqualityTerm =
                    varFirst ? tb.equals(conditionsAndResult.result(), otherTerm)
                            : tb.equals(otherTerm, conditionsAndResult.result());
                JTerm resultTerm = pio.isInAntec() ? tb.imp(conditionTerm, resultEqualityTerm)
                        : tb.and(conditionTerm, resultEqualityTerm);
                resultTerms.add(resultTerm);
            }
            // Add results to goal
            if (inImplication) {
                // Change implication
                JTerm newCondition = tb.or(resultTerms);
                if (negation) {
                    newCondition = tb.not(newCondition);
                }
                JTerm newImplication = tb.imp(newCondition, modalityTerm.sub(0).sub(1));
                JTerm newImplicationWithUpdates = tb.applySequential(updates, newImplication);
                resultGoal.addFormula(new SequentFormula(newImplicationWithUpdates),
                    pio.isInAntec(), false);
            } else {
                // Add result directly as new top level formula
                for (JTerm result : resultTerms) {
                    resultGoal.addFormula(new SequentFormula(result), pio.isInAntec(), false);
                }
            }
            return goals;
        } catch (Exception e) {
            throw new RuleAbortException(e.getMessage());
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Name name() {
        return NAME;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String displayName() {
        return NAME.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return displayName();
    }
}
