/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.QuantifiableVariable;

public class MatchVariableSVInstruction extends MatchSchemaVariableInstruction<VariableSV> {

    protected MatchVariableSVInstruction(VariableSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(JTerm subst, MatchConditions mc, LogicServices services) {
        if (subst.op() instanceof QuantifiableVariable) {
            final JTerm foundMapping = (JTerm) mc.getInstantiations().getInstantiation(op);
            if (foundMapping == null) {
                return addInstantiation(subst, mc, services);
            } else if (foundMapping.op() == subst.op()) {
                return mc;
            }
        }
        return null;
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            LogicServices services) {
        final MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
