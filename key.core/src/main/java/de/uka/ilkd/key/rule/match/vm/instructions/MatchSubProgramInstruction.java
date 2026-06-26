/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.JavaBlock;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

/**
 * Matches the Java program of a modality by running a sub-program of {@code VMInstruction}s over
 * the
 * program tree (with its own cursor), instead of the monolithic {@code MatchProgramInstruction}
 * which delegates to the separate {@code ProgramElement.match} AST matcher. The current element is
 * the modality's {@link JavaBlock} (as for {@code MatchProgramInstruction}); the sub-program runs
 * on
 * its {@code program()}, leaving the outer cursor at the {@code JavaBlock} so the surrounding
 * navigation is unchanged.
 */
public final class MatchSubProgramInstruction implements MatchInstruction {

    private final VMProgramInterpreter program;

    public MatchSubProgramInstruction(VMProgramInterpreter program) {
        this.program = program;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        return program.match(((JavaBlock) actualElement).program(), matchConditions, services);
    }
}
