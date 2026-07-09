/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.ast.JavaProgramElement;

import org.key_project.prover.rules.matcher.compiler.ProgramMatchHook;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.SyntaxElementMatchProgramGenerator.buildProgramInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchProgram;

/**
 * Java-DL implementation of the {@link ProgramMatchHook} program-AST axis: it matches the
 * {@code JavaBlock} program of a modality. The interpreter side reuses the generator's converted
 * program instruction ({@link SyntaxElementMatchProgramGenerator#buildProgramInstruction}, falling
 * back to the monolithic {@code MatchProgramInstruction} when conversion is off or unavailable);
 * the compiled side reuses {@link JavaProgramCompiler#compiledProgramMatcher} (context-block phases
 * + generic {@code getChild} navigation + value-leaf / list-SV delegation). Both sides are derived
 * from the single-source dispatch ({@code JavaProgramMatchPlanBuilder}).
 */
public final class JavaProgramMatchHook implements ProgramMatchHook {

    private final JavaProgramElement prog;
    private final boolean programInstructions;
    private final MatchProgram compiled;

    private JavaProgramMatchHook(JavaProgramElement prog, boolean programInstructions,
            MatchProgram compiled) {
        this.prog = prog;
        this.programInstructions = programInstructions;
        this.compiled = compiled;
    }

    /**
     * @param prog the modality's program pattern
     * @param programInstructions whether the interpreter side converts the program to VM
     *        instructions (otherwise the monolithic {@code MatchProgramInstruction} is used)
     * @return a hook for {@code prog}, or {@code null} if the compiled side cannot handle the
     *         program
     *         (then the enclosing modality falls back to the legacy matcher)
     */
    public static @Nullable JavaProgramMatchHook of(JavaProgramElement prog,
            boolean programInstructions) {
        final MatchProgram compiled = JavaProgramCompiler.compiledProgramMatcher(prog);
        if (compiled == null) {
            return null;
        }
        return new JavaProgramMatchHook(prog, programInstructions, compiled);
    }

    @Override
    public VMInstruction programInstruction() {
        final VMInstruction converted = programInstructions ? buildProgramInstruction(prog) : null;
        return converted != null ? converted : matchProgram(prog);
    }

    @Override
    public MatchProgram compileProgram() {
        return compiled;
    }
}
