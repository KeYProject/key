/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.logic.JavaBlock;

import org.key_project.prover.rules.matcher.compiler.ProgramMatchHook;
import org.key_project.prover.rules.matcher.compiler.ProgramMatchPlan;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.SyntaxElementMatchProgramGenerator.buildProgramInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchProgram;

/**
 * Java-DL implementation of the {@link ProgramMatchHook} SPI (service provider interface): it
 * matches the
 * {@code JavaBlock} program of a modality. The compiled side is the single-source dispatch's plan
 * ({@link JavaProgramMatchPlanBuilder#buildProgramPlan}) and nothing else — it calls no AST
 * {@code match} method; a program the dispatch does not describe yields no hook, and the taclet
 * fails to load with the framework's clear error. The interpreter side reuses the generator's
 * converted program instruction
 * ({@link SyntaxElementMatchProgramGenerator#buildProgramInstruction},
 * falling back to the monolithic {@code MatchProgramInstruction} when conversion is off or
 * unavailable).
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
     * @return a hook for {@code prog}, or {@code null} if the dispatch does not describe the
     *         program (the enclosing modality then has no head and the taclet fails to load with
     *         a clear error)
     */
    public static @Nullable JavaProgramMatchHook of(JavaProgramElement prog,
            boolean programInstructions) {
        final ProgramMatchPlan plan = JavaProgramMatchPlanBuilder.buildProgramPlan(prog);
        if (plan == null || plan.listSV() != null) {
            return null;
        }
        // the plan matches the program element; the modality skeleton hands over the JavaBlock
        final MatchProgram ps = plan.compile();
        final MatchProgram compiled =
            (block, mc, services) -> ps.match(((JavaBlock) block).program(), mc, services);
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
