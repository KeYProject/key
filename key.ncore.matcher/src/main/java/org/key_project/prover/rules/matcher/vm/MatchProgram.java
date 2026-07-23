/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * A program that matches a syntax element against a fixed pattern (the find expression of a
 * taclet).
 * <p>
 * There are two implementations: the {@link VMProgramInterpreter}, which interprets a sequence of
 * {@code VMInstruction}s over a generic cursor, and a compiled variant that navigates the term
 * structure directly (no cursor) for the patterns it supports. Both are interchangeable; which one
 * a
 * {@code VMTacletMatcher} uses is selected at construction time, so the system can always fall back
 * to the pure interpreter.
 */
public interface MatchProgram {

    /**
     * Attempts to match the given syntax element against this program's pattern.
     *
     * @param toMatch the {@link SyntaxElement} to be matched
     * @param mc the initial match conditions; may be extended on success
     * @param services the {@link LogicServices}
     * @return the resulting {@link MatchResultInfo} on success, or {@code null} if no match
     */
    @Nullable
    MatchResultInfo match(SyntaxElement toMatch, MatchResultInfo mc, LogicServices services);
}
