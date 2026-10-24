/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.VariableSV;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Matches a variable schema variable ({@code \variables}): the source term's operator must be a
 * quantifiable variable, and it must be the very variable the schema variable is already
 * instantiated with (or the schema variable is instantiated with it now).
 */
@NullMarked
public class MatchVariableSVInstruction extends MatchSchemaVariableInstruction {

    protected MatchVariableSVInstruction(VariableSV op) {
        super(op);
    }


    @Override
    protected @Nullable MatchResultInfo match(JTerm instantiationCandidate, MatchResultInfo mc,
            LogicServices services) {
        if (instantiationCandidate.op() instanceof QuantifiableVariable qv) {
            final JTerm foundMapping = mc.getInstantiations().getInstantiation(op);
            if (foundMapping == null) {
                return addInstantiation(instantiationCandidate, mc, services);
            } else if (foundMapping.op() == qv) {
                return mc;
            }
        }
        return null;
    }

}
