/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchProgramElementInstruction;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchSubProgramInstruction;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.*;

/**
 * This class generates a matching program for a given syntax element that can be
 * interpreted by the virtual machine's interpreter
 *
 * @see org.key_project.prover.rules.matcher.vm.VMProgramInterpreter
 */
public class SyntaxElementMatchProgramGenerator {

    /**
     * System property ({@code -Dkey.matcher.programInstructions=true}) selecting whether the Java
     * program of a modality is matched by a sub-program of {@link VMInstruction}s (a {@link
     * MatchSubProgramInstruction}) instead of the monolithic {@code MatchProgramInstruction}. Only
     * patterns built from generic-match element kinds + (non-list) program schema variables are
     * converted; anything else (context blocks, loops, value literals, list SVs) falls back to the
     * interpreter. Default {@code false} keeps the existing behaviour.
     * <p>
     * Read at matcher-construction time (i.e. when the taclet base is loaded) rather than once at
     * class load, so toggling it and reloading the proof switches the behaviour.
     */
    public static final String PROGRAM_INSTRUCTIONS_PROPERTY = "key.matcher.programInstructions";

    /**
     * caches, per program-element class, whether it uses the generic {@code match} (no override).
     */
    private static final Map<Class<?>, Boolean> GENERIC_MATCH = new ConcurrentHashMap<>();

    /**
     * creates a matcher for the given pattern
     *
     * @param pattern the {@link JTerm} specifying the pattern
     * @return the specialized matcher for the given pattern
     */
    public static VMInstruction[] createProgram(JTerm pattern) {
        return createProgram(pattern, Boolean.getBoolean(PROGRAM_INSTRUCTIONS_PROPERTY));
    }

    /**
     * creates a matcher for the given pattern, choosing explicitly whether the Java program of a
     * modality is matched by converted {@link VMInstruction} sub-programs ({@code true}) or by the
     * monolithic {@code MatchProgramInstruction} ({@code false}). The production path uses
     * {@link #createProgram(JTerm)} which reads the {@code key.matcher.programInstructions} flag;
     * this overload exists mainly to build both variants in one JVM for differential testing.
     *
     * @param pattern the {@link JTerm} specifying the pattern
     * @param programInstructions whether to convert program matching to VM sub-programs
     * @return the specialized matcher for the given pattern
     */
    public static VMInstruction[] createProgram(JTerm pattern, boolean programInstructions) {
        ArrayList<VMInstruction> program = new ArrayList<>();
        createProgram(pattern, program, programInstructions);
        return program.toArray(new VMInstruction[0]);
    }

    /**
     * creates a matching program for the given pattern. It appends the necessary match instruction
     * to the given list of instructions
     *
     * @param pattern the {@link JTerm} used as pattern for which to create a matcher
     * @param program the list of {@link MatchInstruction} to which the instructions for matching
     *        {@code pattern} are added.
     * @param programInstructions whether to convert program matching to VM sub-programs
     */
    private static void createProgram(JTerm pattern, ArrayList<VMInstruction> program,
            boolean programInstructions) {
        final Operator op = pattern.op();

        final ImmutableArray<QuantifiableVariable> boundVars = pattern.boundVars();

        if (!boundVars.isEmpty()) {
            program.add(matchAndBindVariables(boundVars));
        }

        if (pattern.hasLabels()) {
            program.add(matchTermLabelSV(pattern.getLabels()));
        }

        if (op instanceof SchemaVariable sv) {
            program.add(getMatchInstructionForSV(sv));
            program.add(gotoNextSiblingInstruction());
        } else {
            program.add(getCheckNodeKindInstruction(JTerm.class));
            program.add(gotoNextInstruction());
            switch (op) {
                case ParametricFunctionInstance pfi -> {
                    program.add(getCheckNodeKindInstruction(ParametricFunctionInstance.class));
                    program.add(getSimilarParametricFunctionInstruction(pfi));
                    program.add(gotoNextInstruction());
                    for (int i = 0; i < pfi.getChildCount(); i++) {
                        var arg = (GenericArgument) pfi.getChild(i);
                        if (arg.sort() instanceof GenericSort gs) {
                            program.add(getMatchGenericSortInstruction(gs));
                        } else if (arg.sort() instanceof ParametricSortInstance) {
                            throw new UnsupportedOperationException(
                                "TODO @ DD: Parametric sort in generic args!");
                        } else {
                            program.add(getMatchIdentityInstruction(arg));
                        }
                        program.add(gotoNextInstruction());
                    }
                }
                case ElementaryUpdate elUp -> {
                    program.add(getCheckNodeKindInstruction(ElementaryUpdate.class));
                    program.add(gotoNextInstruction());
                    if (elUp.lhs() instanceof SchemaVariable sv) {
                        program.add(getMatchInstructionForSV(sv));
                        program.add(gotoNextSiblingInstruction());
                    } else if (elUp.lhs() instanceof LocationVariable locVar) {
                        program.add(getMatchIdentityInstruction(locVar));
                        program.add(gotoNextInstruction());
                    }
                }
                case Modality mod -> {
                    program.add(getCheckNodeKindInstruction(Modality.class));
                    program.add(gotoNextInstruction());
                    if (mod.kind() instanceof ModalOperatorSV modKindSV) {
                        program.add(matchModalOperatorSV(modKindSV));
                    } else {
                        program.add(getMatchIdentityInstruction(mod.kind()));
                    }
                    program.add(gotoNextInstruction());
                    final JavaProgramElement prog = pattern.javaBlock().program();
                    final VMInstruction progInstr =
                        programInstructions ? buildProgramInstruction(prog) : null;
                    program.add(progInstr != null ? progInstr : matchProgram(prog));
                    program.add(gotoNextSiblingInstruction());
                }
                default -> {
                    program.add(getMatchIdentityInstruction(op));
                    program.add(gotoNextInstruction());
                }
            }
        }

        if (!boundVars.isEmpty()) {
            for (int i = 0; i < boundVars.size(); i++) {
                program.add(gotoNextSiblingInstruction());
            }
        }

        for (int i = 0; i < pattern.arity(); i++) {
            createProgram(pattern.sub(i), program, programInstructions);
        }

        if (!boundVars.isEmpty()) {
            program.add(unbindVariables(boundVars));
        }
    }

    /**
     * Builds the instruction matching the Java program {@code prog} of a modality by direct tree
     * navigation, or returns {@code null} if {@code prog} uses a construct the converter does not
     * handle (the caller then falls back to the monolithic {@code MatchProgramInstruction}). The
     * program is matched generically by a {@link MatchSubProgramInstruction}.
     */
    private static @Nullable VMInstruction buildProgramInstruction(JavaProgramElement prog) {
        final VMInstruction[] sub = buildProgramSubProgram(prog);
        return sub == null ? null : new MatchSubProgramInstruction(new VMProgramInterpreter(sub));
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
     * construct
     * that is not safe to convert: list schema variables, other schema variables, and element types
     * that override {@code match} (context blocks, loops, value-checking literals, ...).
     */
    private static boolean appendProgram(SyntaxElement pe, List<VMInstruction> out) {
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
        if (!(pe instanceof ProgramElement progEl) || !isGenericMatch(progEl)) {
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

    /**
     * @return whether the element's class uses the generic
     *         {@code match(SourceData, MatchConditions)} (declared in {@code JavaProgramElement} or
     *         {@code JavaNonTerminalProgramElement}: class equality + exact-size child recursion)
     *         rather than its own override.
     */
    static boolean isGenericMatch(ProgramElement pe) {
        return GENERIC_MATCH.computeIfAbsent(pe.getClass(), c -> {
            try {
                final Class<?> declaring =
                    c.getMethod("match", SourceData.class, MatchConditions.class)
                            .getDeclaringClass();
                return declaring == JavaProgramElement.class
                        || declaring == JavaNonTerminalProgramElement.class;
            } catch (NoSuchMethodException e) {
                return false;
            }
        });
    }
}
