/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * Matches a single program element structurally: the current element must have exactly the
 * expected concrete class and number of children (the children are then matched separately, one
 * by one). This is the head check of the structural program plan
 * ({@code org.key_project.prover.rules.matcher.compiler.ProgramStructuralPlan}) and is shared by
 * both back-ends: emitted into the interpreter's instruction stream, and applied directly as the
 * first step of the compiled fixed-arity matcher.
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
