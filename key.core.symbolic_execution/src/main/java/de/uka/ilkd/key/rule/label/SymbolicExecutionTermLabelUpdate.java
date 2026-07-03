/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Set;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;
import de.uka.ilkd.key.rule.*;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
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
        return ImmutableList.<Name>nil().prepend(WhileInvariantRule.INSTANCE.name())
                .prepend(BlockContractInternalRule.INSTANCE.name())
                .prepend(BlockContractExternalRule.INSTANCE.name())
                .prepend(LoopContractInternalRule.INSTANCE.name())
                .prepend(LoopContractExternalRule.INSTANCE.name());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void updateLabels(TermLabelContext context, JTerm newTerm, Set<TermLabel> labels) {
        if (context.rule() instanceof WhileInvariantRule
                && "LoopBodyModality".equals(context.hint())
                || (context.rule() instanceof AbstractAuxiliaryContractRule
                        && ((AbstractBlockContractRule.BlockContractHint) context.hint())
                                .getExceptionalVariable() != null)) {
            TermLabel label = CollectionUtil.searchAndRemove(labels,
                element -> element instanceof SymbolicExecutionTermLabel);
            if (label instanceof SymbolicExecutionTermLabel) {
                int labelID =
                    context.services().getCounter(SymbolicExecutionTermLabel.PROOF_COUNTER_NAME)
                            .getCountPlusPlus();
                labels.add(new SymbolicExecutionTermLabel(labelID));
            }
        }
    }
}
