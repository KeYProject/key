/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Makes sure that {@link SymbolicExecutionUtil#LOOP_BODY_LABEL} is introduced when a
 * {@link WhileInvariantRule} is applied.
 *
 * @author Martin Hentschel
 */
public class LoopBodyTermLabelUpdate implements TermLabelUpdate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return ImmutableSLList.singleton(WhileInvariantRule.INSTANCE.name());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void updateLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, JTerm applicationTerm, JTerm modalityTerm,
            Rule rule, RuleApp ruleApp, Object hint, JTerm tacletTerm, JTerm newTerm,
            Set<TermLabel> labels) {
        if (rule instanceof WhileInvariantRule && "LoopBodyModality".equals(hint)
                && SymbolicExecutionUtil.hasSymbolicExecutionLabel(modalityTerm)) {
            labels.add(SymbolicExecutionUtil.LOOP_BODY_LABEL);
        }
    }
}
