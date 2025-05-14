/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchConditions;

/**
 * Interface that has to be implemented by instructions for the matching virtual machine
 */
public interface MatchInstruction {
    MatchConditions match(PoolSyntaxElementCursor termPosition, MatchConditions matchConditions,
            LogicServices services);
}
