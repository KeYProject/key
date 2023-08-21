/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.*;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.CollectionUtil;

/**
 * Makes sure that the ID of {@link SymbolicExecutionTermLabel}s is increased when a
 * {@link WhileInvariantRule} is applied.
 *
 * @author Martin Hentschel
 */
public class SymbolicExecutionTermLabelUpdate implements TermLabelUpdate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return ImmutableSLList.<Name>nil().prepend(WhileInvariantRule.INSTANCE.name())
                .prepend(BlockContractInternalRule.INSTANCE.name())
                .prepend(BlockContractExternalRule.INSTANCE.name())
                .prepend(LoopContractInternalRule.INSTANCE.name())
                .prepend(LoopContractExternalRule.INSTANCE.name());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void updateLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Term modalityTerm,
            Rule rule, RuleApp ruleApp, Object hint, Term tacletTerm, Operator newTermOp,
            ImmutableArray<Term> newTermSubs, ImmutableArray<QuantifiableVariable> newTermBoundVars,
            JavaBlock newTermJavaBlock, Set<TermLabel> labels) {
        if (rule instanceof WhileInvariantRule && "LoopBodyModality".equals(hint)
                || (rule instanceof AbstractAuxiliaryContractRule
                        && ((AbstractBlockContractRule.BlockContractHint) hint)
                                .getExceptionalVariable() != null)) {
            TermLabel label = CollectionUtil.searchAndRemove(labels,
                element -> element instanceof SymbolicExecutionTermLabel);
            if (label instanceof SymbolicExecutionTermLabel) {
                int labelID = services.getCounter(SymbolicExecutionTermLabel.PROOF_COUNTER_NAME)
                        .getCountPlusPlus();
                labels.add(new SymbolicExecutionTermLabel(labelID));
            }
        }
    }
}
