/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.VariableSV;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

public class MatchVariableSVInstruction extends MatchSchemaVariableInstruction {

    protected MatchVariableSVInstruction(VariableSV op) {
        super(op);
    }


    @Override
    public MatchResultInfo match(SyntaxElement actualElement, MatchResultInfo mc,
            LogicServices services) {
        final JTerm actualTerm = (JTerm) actualElement;
        if (actualTerm.op() instanceof QuantifiableVariable qv) {
            final JTerm foundMapping = mc.getInstantiations().getInstantiation(op);
            if (foundMapping == null) {
                return addInstantiation(actualTerm, mc, services);
            } else if (foundMapping.op() == qv) {
                return mc;
            }
        }
        return null;
    }

}
