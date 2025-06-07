/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.BlockContractValidityTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.CollectionUtil;

import org.jspecify.annotations.NonNull;

/**
 * Makes sure that {@link BlockContractValidityTermLabel} is introduced when a
 * {@link BlockContractInternalRule} is applied.
 *
 * @author Martin Hentschel
 */
public class BlockContractValidityTermLabelUpdate implements TermLabelUpdate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return ImmutableSLList.singleton(BlockContractInternalRule.INSTANCE.name());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void updateLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Term modalityTerm,
            Rule rule, RuleApp ruleApp, @NonNull Object hint, Term tacletTerm, Term newTerm,
            @NonNull Set<TermLabel> labels) {
        if ((rule instanceof BlockContractInternalRule || rule instanceof LoopContractInternalRule)
                && ((BlockContractInternalRule.BlockContractHint) hint)
                        .getExceptionalVariable() != null
                && SymbolicExecutionUtil.hasSymbolicExecutionLabel(modalityTerm)) {
            if (CollectionUtil.search(labels,
                element -> element instanceof BlockContractValidityTermLabel) == null) {
                labels.add(new BlockContractValidityTermLabel(
                    ((BlockContractInternalRule.BlockContractHint) hint).getExceptionalVariable()));
            }
        }
    }
}
