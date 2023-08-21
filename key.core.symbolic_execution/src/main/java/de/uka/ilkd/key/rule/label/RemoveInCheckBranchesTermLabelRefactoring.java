/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule;
import de.uka.ilkd.key.rule.BlockContractExternalRule;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.LoopContractExternalRule;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * This {@link TermLabelRefactoring} removes the supported {@link TermLabel} in check branches.
 * These are:
 * <ul>
 * <li>{@link AbstractAuxiliaryContractRule}: Pre</li>
 * <li>{@link UseOperationContractRule}: Pre</li>
 * <li>{@link UseOperationContractRule}: Null reference</li>
 * <li>{@link WhileInvariantRule}: Invariant Initially Valid</li>
 * </ul>
 *
 * @author Martin Hentschel
 */
public class RemoveInCheckBranchesTermLabelRefactoring implements TermLabelRefactoring {
    /**
     * The {@link Name} of the supported {@link TermLabel}.
     */
    private final Name termLabelNameToRemove;

    /**
     * Constructor.
     *
     * @param termLabelNameToRemove The {@link Name} of the supported {@link TermLabel}.
     */
    public RemoveInCheckBranchesTermLabelRefactoring(Name termLabelNameToRemove) {
        assert termLabelNameToRemove != null;
        this.termLabelNameToRemove = termLabelNameToRemove;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return ImmutableSLList.<Name>nil().prepend(UseOperationContractRule.INSTANCE.name())
                .prepend(WhileInvariantRule.INSTANCE.name())
                .prepend(BlockContractInternalRule.INSTANCE.name())
                .prepend(BlockContractExternalRule.INSTANCE.name())
                .prepend(LoopContractInternalRule.INSTANCE.name())
                .prepend(LoopContractExternalRule.INSTANCE.name());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RefactoringScope defineRefactoringScope(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        if (goal != null) {
            if (rule instanceof UseOperationContractRule
                    && (goal.node().getNodeInfo().getBranchLabel().startsWith("Pre") || goal.node()
                            .getNodeInfo().getBranchLabel().startsWith("Null reference"))) {
                return RefactoringScope.SEQUENT;
            } else if (rule instanceof WhileInvariantRule && goal.node().getNodeInfo()
                    .getBranchLabel().startsWith("Invariant Initially Valid")) {
                return RefactoringScope.SEQUENT;
            } else if (rule instanceof AbstractAuxiliaryContractRule
                    && goal.node().getNodeInfo().getBranchLabel().startsWith("Precondition")) {
                return RefactoringScope.SEQUENT;
            } else {
                return RefactoringScope.NONE;
            }
        } else {
            return RefactoringScope.NONE;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void refactorLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term term, List<TermLabel> labels) {
        labels.removeIf(next -> termLabelNameToRemove.equals(next.name()));
    }
}
