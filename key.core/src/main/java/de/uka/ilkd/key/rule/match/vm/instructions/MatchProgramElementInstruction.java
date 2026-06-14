/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

/**
 * Matches a single program element structurally: the current element must have exactly the expected
 * concrete class and number of children. This mirrors the generic program matching
 * ({@code JavaProgramElement.match} / {@code JavaNonTerminalProgramElement.match}: class equality
 * plus an exact block size), and is only emitted for element types that use that generic match (the
 * compiler falls back to the interpreter's {@code MatchProgramInstruction} for any type that
 * overrides {@code match}, e.g. context blocks, loops or value-checking literals).
 */
public final class MatchProgramElementInstruction implements MatchInstruction {

    private final Class<? extends SyntaxElement> kind;
    private final int childCount;

    public MatchProgramElementInstruction(Class<? extends SyntaxElement> kind, int childCount) {
        this.kind = kind;
        this.childCount = childCount;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        if (actualElement.getClass() == kind && actualElement.getChildCount() == childCount) {
            return matchConditions;
        }
        return null;
    }
}
