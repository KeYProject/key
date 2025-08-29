/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * A {@link MatchInstruction} that checks for syntactic identity between the
 * current {@link SyntaxElement} and a predefined reference element.
 * <p>
 * This instruction succeeds only if the syntax element at the current cursor
 * position is <em>identical</em> (i.e., the same object reference) to the
 * {@link SyntaxElement} provided at construction time.
 * <p>
 * This is useful for matching propositional connectives,
 * most operators etc. where object identity is crucial.
 */
public final class MatchIdentityInstruction implements MatchInstruction {

    /**
     * The syntax element to compare against the current element during matching.
     */
    private final SyntaxElement syntaxElement;

    /**
     * Constructs a new identity-based match instruction.
     *
     * @param syntaxElement the {@link SyntaxElement} that must be identical (reference-equal)
     *        to the current element for the match to succeed
     */
    public MatchIdentityInstruction(SyntaxElement syntaxElement) {
        this.syntaxElement = syntaxElement;
    }

    /**
     * Performs the identity check between the provided {@code actualElement} and
     * the internally stored {@code syntaxElement}.
     *
     * @param actualElement the current syntax element under evaluation
     * @param matchConditions the current match context to return if the identity check succeeds
     * @param services logic services (unused in this implementation)
     * @return the original {@code matchConditions} if the elements have the
     *         same identity (reference-equal), or {@code null} if they are not
     */
    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions,
            LogicServices services) {
        if (syntaxElement == actualElement) {
            return matchConditions;
        }
        return null;
    }
}
