/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * A {@link MatchInstruction} that verifies whether the current {@link SyntaxElement}
 * is an instance of a specific node type.
 * <p>
 * This instruction succeeds if the syntax element currently being matched is
 * an instance of the class (or a subclass) specified at construction time.
 * It does not modify the matching state but filters candidates based on their type.
 * <p>
 * This is useful for enforcing structural expectations during pattern matching,
 * such as ensuring that a node belongs to a particular kind of syntax tree node,
 * e.g., an operator, a quantifier, or a specific term subclass.
 */
public final class CheckNodeKindInstruction implements MatchInstruction {

    /**
     * The expected class or interface the syntax element must be an instance of.
     */
    private final Class<?> nodeType;

    /**
     * Constructs a new instruction that checks for a specific node type.
     *
     * @param nodeType the expected class that the syntax element must be an instance of
     */
    public CheckNodeKindInstruction(Class<?> nodeType) {
        this.nodeType = nodeType;
    }

    /**
     * Checks whether the given {@link SyntaxElement} is an instance of the expected type.
     *
     * @param actualElement the current syntax element under evaluation
     * @param matchConditions the current matching context
     * @param services logic services (unused in this implementation)
     * @return the unchanged {@code matchConditions} if the check passes, or {@code null} if it
     *         fails
     */
    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions,
            LogicServices services) {
        if (nodeType.isInstance(actualElement)) {
            return matchConditions;
        }
        return null;
    }
}
