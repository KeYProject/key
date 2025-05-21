/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchConditions;

/**
 * Interface that has to be implemented by instructions for the matching virtual machine
 */
public interface MatchInstruction
        extends org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction {

    @Override
    default de.uka.ilkd.key.rule.MatchConditions match(PoolSyntaxElementCursor cursor,
            MatchConditions matchConditions,
            LogicServices services) {
        return match(cursor, (de.uka.ilkd.key.rule.MatchConditions) matchConditions, services);
    }


    de.uka.ilkd.key.rule.MatchConditions match(PoolSyntaxElementCursor cursor,
            de.uka.ilkd.key.rule.MatchConditions matchConditions,
            LogicServices services);

}
