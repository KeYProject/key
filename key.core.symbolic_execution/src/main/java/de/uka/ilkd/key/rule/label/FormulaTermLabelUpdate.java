/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.CollectionUtil;

/**
 * The {@link TermLabelUpdate} used to label predicates with a {@link FormulaTermLabel} of add
 * clauses which were not labeled before.
 *
 * @author Martin Hentschel
 */
public class FormulaTermLabelUpdate implements TermLabelUpdate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return null; // Support all rules.
    }

    /**
     * {@inheritDoc}
     */
    public void updateLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Term modalityTerm,
            Rule rule, RuleApp ruleApp, Object hint, Term tacletTerm, Term newTerm,
            Set<TermLabel> labels) {
        if (hint instanceof TacletLabelHint tacletHint) {
            if ((TacletOperation.ADD_ANTECEDENT.equals(tacletHint.getTacletOperation())
                    || TacletOperation.ADD_SUCCEDENT.equals(tacletHint.getTacletOperation()))
                    && (TruthValueTracingUtil.isPredicate(newTerm)
                            || TruthValueTracingUtil.isLogicOperator(newTerm.op(),
                                newTerm.subs()))) {
                if (getTermLabel(labels, FormulaTermLabel.NAME) == null) {
                    TermLabel label = TermLabelManager.findInnerMostParentLabel(
                        applicationPosInOccurrence, FormulaTermLabel.NAME);
                    if (label instanceof FormulaTermLabel oldLabel) {
                        int labelSubID = FormulaTermLabel.newLabelSubID(services, oldLabel);
                        FormulaTermLabel newLabel = new FormulaTermLabel(oldLabel.getMajorId(),
                            labelSubID, Collections.singletonList(oldLabel.getId()));
                        labels.add(newLabel);
                        // Let the PredicateTermLabelRefactoring perform the refactoring, see also
                        // PredicateTermLabelRefactoring#PARENT_REFACTORING_REQUIRED
                        FormulaTermLabelRefactoring.setParentRefactoringRequired(state, true);
                    }
                }
            }
        }
        if (ruleApp instanceof TacletApp ta) {
            if (ta.ifInstsComplete() && ta.ifFormulaInstantiations() != null) {
                Map<SequentFormula, FormulaTermLabel> ifLabels =
                    new LinkedHashMap<>();
                for (IfFormulaInstantiation ifInst : ta.ifFormulaInstantiations()) {
                    FormulaTermLabel ifLabel = StayOnFormulaTermLabelPolicy.searchFormulaTermLabel(
                        ifInst.getConstrainedFormula().formula().getLabels());
                    if (ifLabel != null) {
                        ifLabels.put(ifInst.getConstrainedFormula(), ifLabel);
                    }
                }
                if (!ifLabels.isEmpty()) {
                    if (TruthValueTracingUtil.isLogicOperator(newTerm.op(), newTerm.subs())
                    // || TruthValueEvaluationUtil.isPredicate(newTermOp)
                    ) {
                        for (Entry<SequentFormula, FormulaTermLabel> ifEntry : ifLabels
                                .entrySet()) {
                            FormulaTermLabel ifLabel = ifEntry.getValue();
                            int labelSubID = FormulaTermLabel.newLabelSubID(services, ifLabel);
                            FormulaTermLabel newLabel = new FormulaTermLabel(ifLabel.getMajorId(),
                                labelSubID, Collections.singletonList(ifLabel.getId()));
                            labels.add(newLabel);
                            FormulaTermLabelRefactoring.addSequentFormulaToRefactor(state,
                                ifEntry.getKey());
                        }
                    }
                }
            }
        }
    }

    /**
     * Returns the {@link TermLabel} with the given {@link Name}.
     *
     * @param labels the {@link TermLabel}s to search in.
     * @param name The {@link Name} of the {@link TermLabel} to search.
     * @return The found {@link TermLabel} or {@code} null if no element was found.
     */
    protected TermLabel getTermLabel(Set<TermLabel> labels, final Name name) {
        return CollectionUtil.search(labels,
            element -> element != null && element.name().equals(name));
    }
}
