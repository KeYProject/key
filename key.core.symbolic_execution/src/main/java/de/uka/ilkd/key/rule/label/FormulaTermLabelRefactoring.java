/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.LabelCollection;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.CollectionUtil;

/**
 * The {@link TermLabelRefactoring} used to label predicates with a {@link FormulaTermLabel} on
 * applied loop invariants or operation contracts.
 *
 * @author Martin Hentschel
 */
public class FormulaTermLabelRefactoring implements TermLabelRefactoring {
    /**
     * Key prefix used in {@link TermLabelState} to store that the innermost label was already
     * refactored on a given {@link Goal}.
     */
    private static final String INNER_MOST_PARENT_REFACTORED_PREFIX =
        "innerMostParentRefactoredAtGoal_";

    /**
     * Key used in {@link TermLabelState} by the {@link StayOnOperatorTermLabelPolicy} to indicate
     * that a refactoring below an update ({@link RefactoringScope#APPLICATION_BELOW_UPDATES}) is
     * required, which will be performed by
     * {@link #refactorBelowUpdates(PosInOccurrence, Term, LabelCollection)}.
     * <p>
     * This is for instance required for the following rules:
     * <ul>
     * <li>{@code concrete_and_1}</li>
     * <li>{@code concrete_and_2}</li>
     * <li>{@code concrete_and_3}</li>
     * <li>{@code concrete_and_4}</li>
     * <li>{@code concrete_eq_1}</li>
     * <li>{@code concrete_eq_2}</li>
     * <li>{@code concrete_eq_3}</li>
     * <li>{@code concrete_eq_4}</li>
     * <li>{@code concrete_impl_1}</li>
     * <li>{@code concrete_impl_2}</li>
     * <li>{@code concrete_impl_3}</li>
     * <li>{@code concrete_impl_4}</li>
     * <li>{@code concrete_not_1}</li>
     * <li>{@code concrete_not_2}</li>
     * <li>{@code concrete_or_1}</li>
     * <li>{@code concrete_or_2}</li>
     * <li>{@code concrete_or_3}</li>
     * <li>{@code concrete_or_4}</li>
     * </ul>
     */
    private static final String UPDATE_REFACTORING_REQUIRED = "updateRefactoringRequired";

    /**
     * Key used in {@link TermLabelState} by the {@link FormulaTermLabelUpdate} to indicate that a
     * refactoring of parents
     * ({@link RefactoringScope#APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS}) is
     * required, which will be performed by
     * {@link #refactorInCaseOfNewIdRequired(TermLabelState, Goal, Term, Services, LabelCollection)}.
     * <p>
     * This is for instance required if a rule is applied on a sub term without a
     * {@link FormulaTermLabel} of a parent which has a {@link FormulaTermLabel}. Example rules are:
     * <ul>
     * <li>{@code ifthenelse_split}</li>
     * <li>{@code arrayLengthNotNegative}</li>
     * </ul>
     */
    private static final String PARENT_REFACTORING_REQUIRED = "parentRefactoringRequired";

    /**
     * Key used in {@link TermLabelState} by the {@link FormulaTermLabelUpdate} to indicate that a
     * refactoring of specified {@link SequentFormula}s ({@link RefactoringScope#SEQUENT}) is
     * required, which will be performed by
     * {@link #refactorSequentFormulas(TermLabelState, Services, Term, LabelCollection)}.
     * <p>
     * This is for instance required if the assumes clause of a rule has a {@link FormulaTermLabel}
     * but the application does not have it. Example rules are:
     * <ul>
     * <li>{@code inEqSimp_contradInEq1}</li>
     * </ul>
     */
    private static final String SEQUENT_FORMULA_REFACTORING_REQUIRED =
        "sequentFormulaRefactoringRequired";

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return null; // Support all rules
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RefactoringScope defineRefactoringScope(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        if (shouldRefactorSpecificationApplication(rule, goal, hint)) {
            return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE;
        } else if (isParentRefactoringRequired(state)) {
            return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS;
        } else if (isUpdateRefactoringRequired(state)) {
            return RefactoringScope.APPLICATION_BELOW_UPDATES;
        } else if (containsSequentFormulasToRefactor(state)) {
            return RefactoringScope.SEQUENT;
        } else if (SyntacticalReplaceVisitor.SUBSTITUTION_WITH_LABELS_HINT.equals(hint)) {
            return RefactoringScope.APPLICATION_BELOW_UPDATES;
        } else {
            return RefactoringScope.NONE;
        }
    }

    /**
     * Checks if the given hint requires a refactoring.
     *
     * @param rule The applied {@link Rule}.
     * @param goal The {@link Goal}.
     * @param hint The hint to check.
     * @return {@code true} perform refactoring, {@code false} do not perform refactoring.
     */
    private boolean shouldRefactorSpecificationApplication(Rule rule, Goal goal, Object hint) {
        return TermLabelRefactoring.shouldRefactorOnBuiltInRule(rule, goal, hint);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void refactorLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term term, LabelCollection labels) {
        if (shouldRefactorSpecificationApplication(rule, goal, hint)) {
            refactorSpecificationApplication(term, services, labels, hint);
        } else if (isParentRefactoringRequired(state)) {
            refactorInCaseOfNewIdRequired(state, goal, term, services, labels);
        } else if (isUpdateRefactoringRequired(state)) {
            refactorBelowUpdates(applicationPosInOccurrence, term, labels);
        } else if (containsSequentFormulasToRefactor(state)) {
            refactorSequentFormulas(state, services, term, labels);
        } else if (SyntacticalReplaceVisitor.SUBSTITUTION_WITH_LABELS_HINT.equals(hint)) {
            refactorSubstitution(term, tacletTerm, labels);
        }
    }

    /**
     * Refactors a specification application.
     *
     * @param term The {@link Term} which is now refactored.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param labels The new labels the {@link Term} will have after the refactoring.
     */
    private void refactorSpecificationApplication(Term term, Services services,
            LabelCollection labels, Object hint) {
        if (TruthValueTracingUtil.isPredicate(term)
                || (CloseAfterMerge.FINAL_WEAKENING_TERM_HINT.equals(hint)
                        && TruthValueTracingUtil.isLogicOperator(term))) {
            TermLabel existingLabel = term.getLabel(FormulaTermLabel.NAME);
            if (existingLabel == null) {
                int labelID =
                    services.getCounter(FormulaTermLabel.PROOF_COUNTER_NAME).getCountPlusPlus();
                int labelSubID = FormulaTermLabel.newLabelSubID(services, labelID);
                labels.add(new FormulaTermLabel(labelID, labelSubID));
            }
        }
    }

    /**
     * Refactors in case that the innermost label needs a new ID.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param term The {@link Term} which is now refactored.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param labels The new labels the {@link Term} will have after the refactoring.
     */
    private void refactorInCaseOfNewIdRequired(TermLabelState state, Goal goal, Term term,
            Services services, LabelCollection labels) {
        if (goal != null && !isInnerMostParentRefactored(state, goal)) {
            TermLabel existingLabel = term.getLabel(FormulaTermLabel.NAME);
            if (existingLabel instanceof FormulaTermLabel pLabel) {
                int labelID = pLabel.getMajorId();
                int labelSubID = FormulaTermLabel.newLabelSubID(services, labelID);
                labels.remove(existingLabel);
                labels.add(new FormulaTermLabel(labelID, labelSubID,
                    Collections.singletonList(pLabel.getId())));
                setInnerMostParentRefactored(state, goal, true);
            }
        }
    }

    /**
     * Refactors the {@link Term} below its update.
     *
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param term The {@link Term} which is now refactored.
     * @param labels The new labels the {@link Term} will have after the refactoring.
     */
    private void refactorBelowUpdates(PosInOccurrence applicationPosInOccurrence, Term term,
            LabelCollection labels) {
        Term applicationTerm =
            applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
        FormulaTermLabel applicationLabel = applicationTerm != null
                ? (FormulaTermLabel) applicationTerm.getLabel(FormulaTermLabel.NAME)
                : null;
        if (applicationLabel != null) {
            FormulaTermLabel termLabel = (FormulaTermLabel) term.getLabel(FormulaTermLabel.NAME);
            if (termLabel == null) {
                labels.add(applicationLabel);
            } else {
                labels.remove(termLabel);
                Set<String> beforeIds =
                    new LinkedHashSet<>(Arrays.asList(termLabel.getBeforeIds()));
                beforeIds.add(applicationLabel.getId());
                labels.add(new FormulaTermLabel(termLabel.getMajorId(), termLabel.getMinorId(),
                    beforeIds));
            }
        }
    }

    /**
     * Refactors the specified {@link SequentFormula}s.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param term The {@link Term} which is now refactored.
     * @param labels The new labels the {@link Term} will have after the refactoring.
     */
    private void refactorSequentFormulas(TermLabelState state, Services services, final Term term,
            LabelCollection labels) {
        Set<SequentFormula> sequentFormulas = getSequentFormulasToRefactor(state);
        if (CollectionUtil.search(sequentFormulas, element -> element.formula() == term) != null) {
            FormulaTermLabel termLabel = (FormulaTermLabel) term.getLabel(FormulaTermLabel.NAME);
            if (termLabel != null) {
                labels.remove(termLabel);
                Set<String> beforeIds = new LinkedHashSet<>();
                beforeIds.add(termLabel.getId());
                int labelSubID = FormulaTermLabel.newLabelSubID(services, termLabel);
                labels.add(new FormulaTermLabel(termLabel.getMajorId(), labelSubID, beforeIds));
            }
        }
    }

    /**
     * Refactors the given {@link Term} after a substitution.
     *
     * @param term The {@link Term} to refactor.
     * @param tacletTerm The taclet {@link Term} which provides additional labels to be merged with
     *        the other {@link Term}.
     * @param labels The new labels the {@link Term} will have after the refactoring.
     */
    private void refactorSubstitution(Term term, Term tacletTerm, LabelCollection labels) {
        FormulaTermLabel tacletLabel =
            (FormulaTermLabel) tacletTerm.getLabel(FormulaTermLabel.NAME);
        if (tacletLabel != null) {
            FormulaTermLabel existingLabel =
                (FormulaTermLabel) term.getLabel(FormulaTermLabel.NAME);
            if (existingLabel == null) {
                labels.add(tacletLabel);
            } else {
                List<String> beforeIds =
                    new ArrayList<>(Arrays.asList(existingLabel.getBeforeIds()));
                boolean changed = false;
                if (!beforeIds.contains(tacletLabel.getId())) {
                    changed = true;
                    beforeIds.add(tacletLabel.getId());
                }
                for (String id : tacletLabel.getBeforeIds()) {
                    if (!beforeIds.contains(id)) {
                        changed = true;
                        beforeIds.add(id);
                    }
                }
                if (changed) {
                    labels.remove(existingLabel);
                    labels.add(new FormulaTermLabel(existingLabel.getMajorId(),
                        existingLabel.getMinorId(), beforeIds));
                }
            }
        }
    }

    /**
     * Checks if the innermost parent was already refactored on the given {@link Goal}.
     *
     * @param state The {@link TermLabelState} to read from.
     * @param goal The {@link Goal} to check.
     * @return {@code true} already refactored, {@code false} not refactored yet.
     */
    public static boolean isInnerMostParentRefactored(TermLabelState state, Goal goal) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        return labelState.containsKey(INNER_MOST_PARENT_REFACTORED_PREFIX + goal.node().serialNr());
    }

    /**
     * Defines if the innermost parent was already refactored on the given {@link Goal}.
     *
     * @param state The {@link TermLabelState} to read from.
     * @param goal The {@link Goal} to check.
     * @param refactored {@code true} already refactored, {@code false} not refactored yet.
     */
    public static void setInnerMostParentRefactored(TermLabelState state, Goal goal,
            boolean refactored) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        labelState.put(INNER_MOST_PARENT_REFACTORED_PREFIX + goal.node().serialNr(),
            refactored);
    }

    /**
     * Checks if a refactoring below the updates is required.
     *
     * @param state The {@link TermLabelState} to read from.
     * @return {@code true} refactoring required, {@code false} refactoring is not required.
     */
    public static boolean isUpdateRefactoringRequired(TermLabelState state) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        Object value = labelState.get(UPDATE_REFACTORING_REQUIRED);
        return value instanceof Boolean && (Boolean) value;
    }

    /**
     * Defines if a refactoring below the updates is required.
     *
     * @param state The {@link TermLabelState} to modify.
     * @param required {@code true} refactoring required, {@code false} refactoring is not required.
     */
    public static void setUpdateRefactoringRequired(TermLabelState state, boolean required) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        labelState.put(UPDATE_REFACTORING_REQUIRED, required);
    }

    /**
     * Checks if a refactoring of parents is required.
     *
     * @param state The {@link TermLabelState} to read from.
     * @return {@code true} refactoring required, {@code false} refactoring is not required.
     */
    public static boolean isParentRefactoringRequired(TermLabelState state) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        Object value = labelState.get(PARENT_REFACTORING_REQUIRED);
        return value instanceof Boolean && (Boolean) value;
    }

    /**
     * Defines if a refactoring of parents is required.
     *
     * @param state The {@link TermLabelState} to modify.
     * @param required {@code true} refactoring required, {@code false} refactoring is not required.
     */
    public static void setParentRefactoringRequired(TermLabelState state, boolean required) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        labelState.put(PARENT_REFACTORING_REQUIRED, required);
    }

    /**
     * Checks if {@link SequentFormula}s to refactor are specified.
     *
     * @param state The {@link TermLabelState} to read from.
     * @return {@code true} at least one {@link SequentFormula} needs to be refactored,
     *         {@code false} refactoring is not required.
     */
    public static boolean containsSequentFormulasToRefactor(TermLabelState state) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        @SuppressWarnings("unchecked")
        Set<SequentFormula> sfSet =
            (Set<SequentFormula>) labelState.get(SEQUENT_FORMULA_REFACTORING_REQUIRED);
        return sfSet != null && !sfSet.isEmpty();
    }

    /**
     * Returns the {@link SequentFormula}s to refactor.
     *
     * @param state The {@link TermLabelState} to read from.
     * @return The {@link SequentFormula}s to refactor.
     */
    public static Set<SequentFormula> getSequentFormulasToRefactor(TermLabelState state) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        @SuppressWarnings("unchecked")
        Set<SequentFormula> sfSet =
            (Set<SequentFormula>) labelState.get(SEQUENT_FORMULA_REFACTORING_REQUIRED);
        return sfSet;
    }

    /**
     * Adds the given {@link SequentFormula} for refactoring purpose.
     *
     * @param state The {@link TermLabelState} to modify.
     * @param sf The {@link SequentFormula} to add.
     */
    public static void addSequentFormulaToRefactor(TermLabelState state, SequentFormula sf) {
        Map<Object, Object> labelState = state.getLabelState(FormulaTermLabel.NAME);
        @SuppressWarnings("unchecked")
        Set<SequentFormula> sfSet =
            (Set<SequentFormula>) labelState.get(SEQUENT_FORMULA_REFACTORING_REQUIRED);
        if (sfSet == null) {
            sfSet = new LinkedHashSet<>();
            labelState.put(SEQUENT_FORMULA_REFACTORING_REQUIRED, sfSet);
        }
        sfSet.add(sf);
    }
}
