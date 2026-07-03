/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.LabelCollection;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;

import org.key_project.prover.rules.Rule;
import org.key_project.prover.sequent.SequentFormula;

/**
 * <p>
 * A {@link TermLabelRefactoring} is used by {@link TermLabelManager#refactorGoal} to refactor the
 * labels of each visited {@link JTerm}.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained during proof
 * construction read the documentation of interface {@link TermLabel}.
 * </p>
 *
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelRefactoring extends RuleSpecificTask {

    /**
     * <p>
     * Determines whether any refactorings should be applied on an application of the given
     * </p>
     * {@link BuiltInRule}.
     * <p>
     * If you perform refactorings despite this method returning false, KeY will throw an exception
     * because the formula that contains the modality in which the contract was applied does not
     * have a FormulaTag.
     * </p>
     *
     * @param rule the rule being applied.
     * @param goal the goal on which the rule is being applied.
     * @param hint an optional hint passed from the active rule to describe the term which should be
     *        created.
     * @return whether any refactorings should be applied on an application of the given rule.
     */
    static boolean shouldRefactorOnBuiltInRule(Rule rule, Goal goal, Object hint) {
        if (goal != null) {
            Proof proof = goal.proof();
            if ((rule instanceof WhileInvariantRule
                    && WhileInvariantRule.INITIAL_INVARIANT_ONLY_HINT.equals(hint))
                    || (rule instanceof WhileInvariantRule
                            && WhileInvariantRule.FULL_INVARIANT_TERM_HINT.equals(hint))
                    || (rule instanceof UseOperationContractRule
                            && UseOperationContractRule.FINAL_PRE_TERM_HINT.equals(hint))
                    || (rule instanceof AbstractAuxiliaryContractRule
                            && AbstractAuxiliaryContractRule.FULL_PRECONDITION_TERM_HINT
                                    .equals(hint))
                    || (rule instanceof AbstractAuxiliaryContractRule
                            && AbstractAuxiliaryContractRule.NEW_POSTCONDITION_TERM_HINT
                                    .equals(hint))
                    || (rule instanceof CloseAfterMerge
                            && CloseAfterMerge.FINAL_WEAKENING_TERM_HINT.equals(hint))) {
                ProofOblInput problem =
                    proof.getServices().getSpecificationRepository().getProofOblInput(proof);
                if (problem instanceof AbstractOperationPO) {
                    return ((AbstractOperationPO) problem).isAddSymbolicExecutionLabel();
                } else {
                    return false;
                }
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

    /**
     * Defines if a refactoring is required and if so in which {@link RefactoringScope}.
     *
     * @param context the {@link TermLabelContext} of the current rule application
     * @return The required {@link RefactoringScope}.
     */
    RefactoringScope defineRefactoringScope(TermLabelContext context);

    /**
     * This method is used to refactor the labels of the given {@link JTerm}.
     *
     * @param context the {@link TermLabelContext} of the current rule application
     * @param term The {@link JTerm} which is now refactored.
     * @param labels The new labels the {@link JTerm} will have after the refactoring.
     */
    void refactorLabels(TermLabelContext context, JTerm term, LabelCollection labels);

    /**
     * Possible refactoring scopes.
     *
     * @author Martin Hentschel
     */
    enum RefactoringScope {
        /**
         * No refactoring required.
         */
        NONE,

        /**
         * Refactor the child below the updates computed via
         * {@link TermBuilder#goBelowUpdates(JTerm)}
         */
        APPLICATION_BELOW_UPDATES,

        /**
         * Refactor children and grandchildren of the application term.
         */
        APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE,

        /**
         * Refactor the {@link SequentFormula} on which the rule is applied.
         */
        APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS,

        /**
         * Refactor the whole sequent.
         */
        SEQUENT
    }
}
