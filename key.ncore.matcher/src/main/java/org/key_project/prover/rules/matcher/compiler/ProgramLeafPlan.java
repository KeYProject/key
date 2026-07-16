/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextSiblingInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * A leaf of the program plan tree: an element matched by a single {@code instruction}, with no
 * child plans (the instruction itself may bind a whole source subtree, as for a program schema
 * variable). The language front-end supplies the instruction: a schema-variable match, a
 * value-comparison, whatever the construct needs. Both back-ends use the same instruction object,
 * so the match semantics exist in exactly one place: {@link #emit} appends it (plus the cursor
 * advance), {@link #compile} applies it directly.
 */
public final class ProgramLeafPlan implements ProgramMatchPlan {

    /** the pattern element this leaf matches; kept for {@link #toString} only. */
    private final SyntaxElement pattern;
    private final MatchInstruction instruction;

    public ProgramLeafPlan(SyntaxElement pattern, MatchInstruction instruction) {
        this.pattern = pattern;
        this.instruction = instruction;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(instruction);
        out.add(GotoNextSiblingInstruction.INSTANCE);
    }

    @Override
    public MatchProgram compile() {
        return instruction::match;
    }

    @Override
    public String toString() {
        return "leaf(" + pattern + ")";
    }
}
