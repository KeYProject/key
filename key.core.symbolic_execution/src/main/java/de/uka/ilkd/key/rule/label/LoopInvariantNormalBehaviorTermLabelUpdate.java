/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Set;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

/**
 * Makes sure that {@link SymbolicExecutionUtil#LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL} is introduced
 * when a {@link WhileInvariantRule} is applied.
 *
 * @author Martin Hentschel
 */
public class LoopInvariantNormalBehaviorTermLabelUpdate implements TermLabelUpdate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return ImmutableList.singleton(WhileInvariantRule.INSTANCE.name());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void updateLabels(TermLabelContext context, JTerm newTerm, Set<TermLabel> labels) {
        if (context.rule() instanceof WhileInvariantRule
                && "LoopBodyImplication".equals(context.hint())
                && SymbolicExecutionUtil.hasSymbolicExecutionLabel(context.modalityTerm())) {
            labels.add(SymbolicExecutionUtil.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL);
        }
    }
}
