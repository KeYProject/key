/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.ast.ContextStatementBlock;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchContextStatementBlockInstruction;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchSubProgramInstruction;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.compiler.ProgramMatchPlan;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.rules.matcher.vm.instruction.MatchProgramElementInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.*;

/**
 * Converts the Java program of a modality into VM match-instructions ({@link VMInstruction}s) by
 * direct tree navigation, for the interpreter side of the match-plan framework (used by the Java
 * {@link org.key_project.prover.rules.matcher.compiler.ProgramMatchHook}). The conversion is off by
 * default and selected by {@link JavaMatchPlanBuilder#PROGRAM_INSTRUCTIONS_PROPERTY}; when off (or
 * for a program the conversion cannot express, e.g. one containing a list schema variable), the
 * interpreter matches the whole program with the monolithic {@code MatchProgramInstruction}. The
 * term skeleton itself is built by {@link JavaMatchPlanBuilder}; this class asks the single-source
 * dispatch ({@link JavaProgramMatchPlanBuilder}) per element first and keeps its own per-construct
 * conversion only as a safety net beneath it.
 *
 * @see org.key_project.prover.rules.matcher.vm.VMProgramInterpreter
 */
public class SyntaxElementMatchProgramGenerator {

    /**
     * Builds the instruction matching the Java program {@code prog} of a modality by direct tree
     * navigation, or returns {@code null} if {@code prog} uses a construct the converter does not
     * handle (the caller then falls back to the monolithic {@code MatchProgramInstruction}). A
     * top-level {@link ContextStatementBlock} (the {@code .. ...} pattern of symbolic-execution
     * taclets) is matched by a {@link MatchContextStatementBlockInstruction} that converts only the
     * active-statement matching; any other program is matched generically by a
     * {@link MatchSubProgramInstruction}.
     */
    static @Nullable VMInstruction buildProgramInstruction(JavaProgramElement prog) {
        if (prog instanceof ContextStatementBlock csb) {
            final VMInstruction[] active = buildContextActiveStatementsProgram(csb);
            return active == null ? null
                    : new MatchContextStatementBlockInstruction(csb,
                        new VMProgramInterpreter(active));
        }
        final VMInstruction[] sub = buildProgramSubProgram(prog);
        return sub == null ? null : new MatchSubProgramInstruction(new VMProgramInterpreter(sub));
    }

    /**
     * Builds a sub-program matching the active statements of the context block {@code csb} (its
     * children from the active offset, i.e. skipping the execution context if present), or returns
     * {@code null} if any active statement uses a construct the converter does not handle. The
     * resulting program is meant to be run via
     * {@link VMProgramInterpreter#matchChildrenFrom(org.key_project.logic.SyntaxElement, int, org.key_project.prover.rules.instantiation.MatchResultInfo, org.key_project.logic.LogicServices)}
     * starting at the located source child, so that each per-statement matcher consumes exactly one
     * source child -- mirroring {@code matchChildren} on the interpreter side.
     */
    private static VMInstruction @Nullable [] buildContextActiveStatementsProgram(
            ContextStatementBlock csb) {
        final int offset = csb.getExecutionContext() == null ? 0 : 1;
        final List<VMInstruction> out = new ArrayList<>();
        for (int i = offset, n = csb.getChildCount(); i < n; i++) {
            if (!appendProgram(csb.getChildAt(i), out)) {
                return null;
            }
        }
        return out.toArray(new VMInstruction[0]);
    }

    /**
     * Builds a sub-program of {@link VMInstruction}s matching the given Java program by direct tree
     * navigation, or returns {@code null} if the program uses a construct the converter does not
     * handle (the caller then falls back to the monolithic {@code MatchProgramInstruction}).
     */
    private static VMInstruction @Nullable [] buildProgramSubProgram(JavaProgramElement prog) {
        final List<VMInstruction> out = new ArrayList<>();
        return appendProgram(prog, out) ? out.toArray(new VMInstruction[0]) : null;
    }

    /**
     * Appends instructions matching {@code pe} (and its subtree) to {@code out}, mirroring the
     * generic program match (class equality + exact-size child recursion) and reusing the existing
     * program-SV instruction. Returns {@code false} (leaving {@code out} unusable) for any
     * construct that is not safe to convert: list schema variables, other schema variables, and
     * element types that override {@code match} (context blocks, loops, value-checking literals,
     * ...).
     */
    private static boolean appendProgram(SyntaxElement pe, List<VMInstruction> out) {
        // The single-source dispatch first: it derives these interpreter instructions and the
        // compiled step from one description. A variable-arity list SV is compiled-only
        // ({@code interpretable() == false}), so a program containing one falls through to the
        // legacy logic below (which itself falls back to the monolithic matcher); a construct the
        // dispatch does not describe falls through the same way (safety net).
        final ProgramMatchPlan plan = JavaProgramMatchPlanBuilder.buildProgramPlan(pe);
        if (plan != null && plan.interpretable()) {
            plan.emit(out);
            return true;
        }
        if (pe instanceof ProgramSV psv) {
            if (psv.isListSV()) {
                return false; // list SV -> variable block size, leave it to the interpreter
            }
            out.add(getMatchInstructionForSV(psv));
            out.add(gotoNextSiblingInstruction());
            return true;
        }
        if (pe instanceof SchemaVariable) {
            return false; // other schema variables in programs: be safe, fall back
        }
        if (!(pe instanceof ProgramElement progEl)
                || !JavaProgramMatchPlanBuilder.isGenericMatch(progEl)) {
            return false; // overrides match (context block, loop, value literal, ...) -> fall back
        }
        final int childCount = pe.getChildCount();
        out.add(new MatchProgramElementInstruction(pe.getClass(), childCount));
        out.add(gotoNextInstruction());
        for (int i = 0; i < childCount; i++) {
            if (!appendProgram(pe.getChild(i), out)) {
                return false;
            }
        }
        return true;
    }

}
