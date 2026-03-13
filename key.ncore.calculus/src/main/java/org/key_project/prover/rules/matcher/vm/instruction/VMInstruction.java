/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * Represents a single instruction in the matching virtual machine used by the KeY system.
 * <p>
 * Implementations of this interface define specific matching operations that are executed
 * during the interpretation of a matching program. These operations work on a
 * {@link PoolSyntaxElementCursor}, which provides navigational access to a
 * {@link org.key_project.logic.SyntaxElement}, and attempt to update or extend a given
 * {@link MatchResultInfo} object with the result of the operation.
 * <p>
 * If an instruction fails, it causes the match to abort.
 *
 * @see org.key_project.prover.rules.matcher.vm.VMProgramInterpreter
 */
public interface VMInstruction {

    /**
     * Executes the matching operation defined by this instruction.
     * <p>
     * This method attempts to match a portion of the current syntax element (as navigated by the
     * {@code cursor}) according to the logic defined in the implementing instruction.
     * The result is either an updated {@link MatchResultInfo} if the match succeeds,
     * or {@code null} if the match fails.
     *
     * @param cursor the cursor navigating the syntax element to be matched
     * @param matchResultInfo the current match context and constraints; may be extended if matching
     *        succeeds
     * @param services logic services providing utility functions needed for matching
     * @return the updated {@link MatchResultInfo} on success, or {@code null} if the match fails
     */
    @Nullable
    MatchResultInfo match(PoolSyntaxElementCursor cursor, MatchResultInfo matchResultInfo,
            LogicServices services);
}
