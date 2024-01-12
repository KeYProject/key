/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.java.CollectionUtil;

/**
 * This {@link TermLabelPolicy} maintains a {@link FormulaTermLabel} on predicates.
 *
 * @author Martin Hentschel
 */
public class StayOnFormulaTermLabelPolicy implements TermLabelPolicy {
    /**
     * {@inheritDoc}
     */
    @Override
    public TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm,
            Term newTerm, TermLabel label) {
        // Maintain label if new Term is a predicate
        if (TruthValueTracingUtil.isPredicate(newTerm.op())
                || TruthValueTracingUtil.isLogicOperator(newTerm.op(), newTerm.subs())) {
            assert label instanceof FormulaTermLabel;
            FormulaTermLabel formulaLabel = (FormulaTermLabel) label;
            FormulaTermLabel originalLabel = searchFormulaTermLabel(newTerm.getLabels());
            FormulaTermLabel mostImportantLabel =
                originalLabel != null ? originalLabel : formulaLabel;
            // May change sub ID if logical operators like junctors are used
            boolean newLabelIdRequired = false;
            Set<String> originalLabelIds = new LinkedHashSet<>();
            if (hint instanceof TacletLabelHint tacletHint) {
                if (isBelowIfThenElse(tacletHint.getTacletTermStack())) {
                    return null; // Do not label children of if-then-else. They are labeled when a
                                 // rule rewrites them outside of the if-then-else.
                }
                if (TacletOperation.ADD_ANTECEDENT.equals(tacletHint.getTacletOperation())
                        || TacletOperation.ADD_SUCCEDENT.equals(tacletHint.getTacletOperation())
                        || TacletOperation.REPLACE_TO_ANTECEDENT
                                .equals(tacletHint.getTacletOperation())
                        || TacletOperation.REPLACE_TO_SUCCEDENT
                                .equals(tacletHint.getTacletOperation())
                        || TacletOperation.REPLACE_AT_ANTECEDENT
                                .equals(tacletHint.getTacletOperation())
                        || TacletOperation.REPLACE_AT_SUCCEDENT
                                .equals(tacletHint.getTacletOperation())) {
                    if (originalLabel == null) { // Do not give a new ID if the term has already one
                                                 // (see rule: impRight)
                        newLabelIdRequired = true;
                        originalLabelIds.add(mostImportantLabel.getId());
                    }
                }
                if (tacletHint.getSequentFormula() != null) {
                    if (!TruthValueTracingUtil.isPredicate(tacletHint.getSequentFormula())) {
                        newLabelIdRequired = true;
                    }
                } else if (tacletHint.getTerm() != null) {
                    boolean topLevel = isTopLevel(tacletHint, tacletTerm);
                    if (!topLevel && !TruthValueTracingUtil.isPredicate(tacletHint.getTerm())) {
                        newLabelIdRequired = true;
                    }
                }
                if (mostImportantLabel != formulaLabel || newLabelIdRequired) { // Without support
                                                                                // of quantors '&&
                                                                                // topLevel' can be
                                                                                // added.
                    originalLabelIds.add(formulaLabel.getId());
                }
            }
            // Replace label with a new one with increased sub ID.
            if (newLabelIdRequired) {
                if (originalLabel != null) {
                    originalLabelIds.add(originalLabel.getId());
                }
                int labelSubID = FormulaTermLabel.newLabelSubID(services, mostImportantLabel);
                if (!originalLabelIds.isEmpty()) {
                    return new FormulaTermLabel(mostImportantLabel.getMajorId(), labelSubID,
                        originalLabelIds);
                } else {
                    return new FormulaTermLabel(mostImportantLabel.getMajorId(), labelSubID);
                }
            } else {
                if (!originalLabelIds.isEmpty()) {
                    return new FormulaTermLabel(mostImportantLabel.getMajorId(),
                        mostImportantLabel.getMinorId(), originalLabelIds);
                } else {
                    return label;
                }
            }
        } else if (UpdateApplication.UPDATE_APPLICATION.equals(newTerm.op())) {
            Term target = newTerm.subs().get(UpdateApplication.targetPos());
            TermLabel targetLabel = target.getLabel(FormulaTermLabel.NAME);
            if (targetLabel instanceof FormulaTermLabel) {
                if (applicationPosInOccurrence != null) {
                    Term appliationTerm = applicationPosInOccurrence.subTerm();
                    TermLabel applicationLabel = appliationTerm.getLabel(FormulaTermLabel.NAME);
                    if (applicationLabel instanceof FormulaTermLabel) {
                        // Let the PredicateTermLabelRefactoring perform the refactoring, see also
                        // PredicateTermLabelRefactoring#UPDATE_REFACTORING_REQUIRED
                        FormulaTermLabelRefactoring.setUpdateRefactoringRequired(state, true);
                    }
                }
            }
            return null;
        } else if (newTerm.op() instanceof SubstOp) { // Such operations perform for instance
                                                      // skolemization (e.g. rule allRight)
            return label;
        } else {
            return null;
        }
    }

    /**
     * Checks if the currently treated taclet {@link Term} is a child of an if-then-else operation.
     *
     * @param visitStack The taclet {@link Term} stack.
     * @return {@code true} is below if-then-else, {@code false} otherwise.
     */
    protected boolean isBelowIfThenElse(Deque<Term> visitStack) {
        if (visitStack != null) {
            return CollectionUtil.search(visitStack,
                element -> element.op() == IfThenElse.IF_THEN_ELSE) != null;
        } else {
            return false;
        }
    }

    /**
     * Searches the {@link FormulaTermLabel} in the given {@link TermLabel}s.
     *
     * @param labels The {@link TermLabel}s to search in.
     * @return The found {@link FormulaTermLabel} or {@code null} if not available.
     */
    public static FormulaTermLabel searchFormulaTermLabel(ImmutableArray<TermLabel> labels) {
        TermLabel result =
            CollectionUtil.search(labels, element -> element instanceof FormulaTermLabel);
        return (FormulaTermLabel) result;
    }

    /**
     * Checks if the given taclet {@link Term} is top level.
     *
     * @param tacletHint The {@link TacletLabelHint} to use.
     * @param tacletTerm The taclet {@link Term} to check.
     * @return {@code true} is top level, {@code false} is not top level.
     */
    protected boolean isTopLevel(TacletLabelHint tacletHint, Term tacletTerm) {
        if (TacletOperation.REPLACE_TERM.equals(tacletHint.getTacletOperation())) {
            return tacletHint.getTerm() == tacletTerm;
        } else {
            return tacletHint.getSequentFormula().formula() == tacletTerm;
        }
    }
}
