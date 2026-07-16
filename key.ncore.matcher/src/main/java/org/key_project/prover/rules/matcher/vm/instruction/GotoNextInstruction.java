/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

/**
 * A {@link VMInstruction} that advances the {@link PoolSyntaxElementCursor}
 * to the next element in the current syntax structure.
 * <p>
 * This instruction unconditionally updates the cursor to point to the next
 * child to be visited.
 * It does not perform any matching logic itself and always returns the current
 * {@link MatchResultInfo} unchanged.
 * <p>
 * Typically used in a sequence of instructions where traversal of the
 * syntax tree is required before further matching steps.
 */
public final class GotoNextInstruction implements VMInstruction {

    /**
     * Singleton instance of this instruction, as it is stateless and reusable.
     */
    public static final GotoNextInstruction INSTANCE = new GotoNextInstruction();

    /**
     * Private constructor to enforce singleton usage via {@link #INSTANCE}.
     */
    private GotoNextInstruction() {
    }

    /**
     * Advances the cursor to the next syntax element.
     *
     * @param cursor the navigation cursor used to traverse the syntax tree
     * @param matchConditions the current match context, returned unchanged
     * @param services logic services
     * @return the unchanged {@link MatchResultInfo}
     */
    @Override
    public MatchResultInfo match(PoolSyntaxElementCursor cursor,
            MatchResultInfo matchConditions,
            LogicServices services) {
        cursor.gotoNext();
        return matchConditions;
    }
}
