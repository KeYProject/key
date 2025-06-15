/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

/**
 * A {@link VMInstruction} that moves the {@link PoolSyntaxElementCursor}
 * to the next sibling of the current syntax element.
 * <p>
 * This instruction is used to traverse horizontally within the syntax tree structure—
 * typically from one argument or subcomponent of a compound term to the next.
 * It does not perform any pattern matching itself and always returns the current
 * {@link MatchResultInfo} unchanged.
 * <p>
 * Useful in instruction sequences that iterate over multiple components of a node.
 */
public final class GotoNextSiblingInstruction implements VMInstruction {

    /**
     * Singleton instance of this instruction, since it holds no internal state.
     */
    public static final GotoNextSiblingInstruction INSTANCE = new GotoNextSiblingInstruction();

    /**
     * Private constructor to enforce singleton usage through {@link #INSTANCE}.
     */
    private GotoNextSiblingInstruction() {
    }

    /**
     * Moves the cursor to the next sibling of the current syntax element.
     *
     * @param cursor the navigation cursor for traversing the syntax structure
     * @param matchConditions the current matching state, returned unchanged
     * @param services logic services (not used in this instruction)
     * @return the unchanged {@code matchConditions}
     */
    @Override
    public MatchResultInfo match(PoolSyntaxElementCursor cursor,
            MatchResultInfo matchConditions,
            LogicServices services) {
        cursor.gotoNextSibling();
        return matchConditions;
    }
}
