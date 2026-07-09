/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * A specialized {@link VMInstruction} for match operations that do not navigate or
 * modify the {@link PoolSyntaxElementCursor}, but operate directly on the current
 * {@link SyntaxElement} to which the cursor points.
 * <p>
 * This interface provides a convenience default implementation of the
 * {@link VMInstruction#match(PoolSyntaxElementCursor, MatchResultInfo, LogicServices)} method,
 * delegating to a simplified match method that accepts only the current syntax element.
 * <p>
 * It is intended for use by instructions whose behavior depends solely on evaluating
 * the current element without needing to change the cursor’s position or context.
 *
 * @see VMInstruction
 * @see SyntaxElement
 * @see PoolSyntaxElementCursor
 */
public interface MatchInstruction extends VMInstruction {

    /**
     * Default implementation of the matching operation defined by {@link VMInstruction}.
     * <p>
     * This implementation retrieves the current {@link SyntaxElement} from the
     * {@link PoolSyntaxElementCursor} and delegates the matching logic to
     * {@link #match(SyntaxElement, MatchResultInfo, LogicServices)}.
     *
     * @param cursor the cursor pointing to the syntax element to match
     * @param matchResultInfo the current matching state and constraints
     * @param services utility services for logic operations
     * @return the updated {@link MatchResultInfo} if the match succeeds,
     *         or {@code null} if it fails
     */
    @Override
    default @Nullable MatchResultInfo match(PoolSyntaxElementCursor cursor,
            MatchResultInfo matchResultInfo,
            LogicServices services) {
        return match(cursor.getCurrentElement(), matchResultInfo, services);
    }

    /**
     * Executes the matching operation against the specified {@link SyntaxElement},
     * without using or altering the cursor.
     *
     * @param actualElement the syntax element currently under evaluation
     * @param matchConditions the current match constraints and context
     * @param services logic services used for performing the match
     * @return the result of the match, or {@code null} if the match fails
     */
    @Nullable
    MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services);
}
