/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ContextStatementBlock;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.ProgramChildrenMatcher;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchInstructionForSV;

/**
 * Compiles the cursor-free matcher for the Java program of a modality, used by the Java
 * {@link org.key_project.prover.rules.matcher.compiler.ProgramMatchHook} (the compiled side of the
 * match-plan framework). It navigates the Java AST directly via {@code getChild(i)} instead of a
 * cursor, mirroring the converted program VM instructions of
 * {@link SyntaxElementMatchProgramGenerator}.
 *
 * <p>
 * A top-level {@link ContextStatementBlock} keeps phases (1)(2)(4) of the context match in
 * {@code ContextStatementBlock.match} and compiles only phase (3); generic structural elements are
 * matched by class equality + exact-size child recursion; elements with their own {@code match}
 * (value literals, type references, loops, ...) and generic elements with variable-arity children
 * (a
 * list schema variable {@code #slist}) are reused cursor-free by {@linkplain #delegateToMatch
 * delegating to their own match}.
 *
 * @see org.key_project.prover.rules.matcher.vm.VMProgramInterpreter
 */
final class JavaProgramCompiler {

    private JavaProgramCompiler() {}

    /**
     * A single compiled matching step over a program (sub)element. Navigates the Java AST directly
     * via {@code getChild(i)} instead of a cursor, mirroring the converted program VM instructions.
     */
    @FunctionalInterface
    private interface ProgStep {
        @Nullable
        MatchResultInfo match(SyntaxElement actual, MatchResultInfo mc, LogicServices services);
    }

    /**
     * Compiles the cursor-free matcher for the Java program {@code prog} of a modality, applied
     * directly to the source {@link JavaBlock} (it extracts the block's program element). A
     * top-level
     * {@link ContextStatementBlock} keeps phases (1)(2)(4) of the context match in
     * {@code ContextStatementBlock.match} and compiles only phase (3) (each active statement
     * consumes
     * one source child), unless an active statement is variable-arity (a list SV) or otherwise
     * uncompilable -- then the whole context match is delegated to
     * {@code ContextStatementBlock.match}
     * (its {@code matchChildren} handles list SVs) while the surrounding term skeleton stays
     * compiled.
     * Any other program is compiled by {@link #compileProgram}. Returns {@code null} only if that
     * generic compilation cannot handle the program.
     */
    static @Nullable MatchProgram compiledProgramMatcher(JavaProgramElement prog) {
        if (prog instanceof ContextStatementBlock csb) {
            final ProgStep[] active = compileActiveStatements(csb);
            if (active != null) {
                // phase (3) of the context match, cursor-free: each active statement consumes one
                // child
                final ProgramChildrenMatcher phase3 = (parent, startChild, mc, services) -> {
                    MatchResultInfo r = mc;
                    for (int k = 0; k < active.length; k++) {
                        r = active[k].match(parent.getChild(startChild + k), r, services);
                        if (r == null) {
                            return null;
                        }
                    }
                    return r;
                };
                // phases (1)(2)(4) stay in ContextStatementBlock.match; only phase (3) is compiled
                return (block, mc, services) -> csb.match(
                    new SourceData(((JavaBlock) block).program(), -1, (Services) services),
                    (MatchConditions) mc, phase3);
            }
            // an active statement is variable-arity (a list SV) or otherwise uncompilable:
            // delegate the whole context match to the interpreter (its matchChildren handles
            // list SVs); the surrounding term skeleton stays compiled
            return (block, mc, services) -> csb.match(
                new SourceData(((JavaBlock) block).program(), -1, (Services) services),
                (MatchConditions) mc);
        }
        final ProgStep ps = compileProgram(prog);
        if (ps == null) {
            return null;
        }
        return (block, mc, services) -> ps.match(((JavaBlock) block).program(), mc, services);
    }

    /**
     * Compiles a Java program (sub)element: a generic-match element with a fixed, one-source-child
     * structure is matched by direct {@code getChild} navigation (class equality + exact-size child
     * recursion); a non-list program schema variable reuses its program-SV instruction. Anything
     * else that is still a {@link ProgramElement} -- an element with its own {@code match} (value
     * literals, type references, loops, ...) <em>or</em> a generic element whose children are not a
     * fixed one-to-one structure (e.g. they contain a list schema variable {@code #slist}) -- is
     * matched cursor-free by {@linkplain #delegateToMatch delegating to its own match}. Returns
     * {@code null} only for a list schema variable on its own (variable arity: its enclosing
     * element
     * delegates) and for non-program schema variables.
     */
    private static @Nullable ProgStep compileProgram(SyntaxElement pe) {
        if (pe instanceof ProgramSV psv) {
            if (psv.isListSV()) {
                // a list SV by itself is variable-arity; the enclosing element delegates instead
                return null;
            }
            final MatchInstruction svInstr = getMatchInstructionForSV(psv);
            return svInstr::match;
        }
        if (pe instanceof SchemaVariable) {
            return null; // other schema variables in programs: be safe, fall back
        }
        if (!(pe instanceof ProgramElement progEl)) {
            return null;
        }
        if (SyntaxElementMatchProgramGenerator.isGenericMatch(progEl)) {
            final int childCount = pe.getChildCount();
            final ProgStep[] subs = new ProgStep[childCount];
            boolean fixedStructure = true;
            for (int i = 0; i < childCount; i++) {
                final ProgStep s = compileProgram(pe.getChild(i));
                if (s == null) {
                    fixedStructure = false; // e.g. a list SV child -> not one-to-one
                    break;
                }
                subs[i] = s;
            }
            if (fixedStructure) {
                final Class<? extends SyntaxElement> kind = pe.getClass();
                return (actual, mc, services) -> {
                    if (actual.getClass() != kind || actual.getChildCount() != childCount) {
                        return null;
                    }
                    MatchResultInfo r = mc;
                    for (int i = 0; i < childCount; i++) {
                        r = subs[i].match(actual.getChild(i), r, services);
                        if (r == null) {
                            return null;
                        }
                    }
                    return r;
                };
            }
        }
        // an element with its own match (value literals, TypeRef, SchematicFieldReference,
        // VariableSpecification, loops, ...) or a generic element with variable-arity children
        // (a list SV): reuse its own match cursor-free (see delegateToMatch)
        return delegateToMatch(progEl);
    }

    /**
     * Matches {@code progEl} by reusing its own {@code match(SourceData, MatchConditions)}
     * cursor-free, exactly as {@code MatchProgramInstruction} does at the program root. This keeps
     * the surrounding program compiled (only this sub-element delegates) and is
     * behaviour-preserving
     * by construction: it is the very match the interpreter would call, including the
     * {@code matchChildren} handling of list schema variables.
     */
    private static ProgStep delegateToMatch(ProgramElement progEl) {
        return (actual, mc, services) -> progEl.match(
            new SourceData((ProgramElement) actual, -1, (Services) services), (MatchConditions) mc);
    }

    /**
     * Compiles the active statements of a context block (its children from the active offset, i.e.
     * skipping the execution context if present), or returns {@code null} if any active statement
     * uses a construct the compiler does not handle.
     */
    private static ProgStep @Nullable [] compileActiveStatements(ContextStatementBlock csb) {
        final int offset = csb.getExecutionContext() == null ? 0 : 1;
        final ProgStep[] active = new ProgStep[csb.getChildCount() - offset];
        for (int i = offset, n = csb.getChildCount(); i < n; i++) {
            final ProgStep s = compileProgram(csb.getChildAt(i));
            if (s == null) {
                return null;
            }
            active[i - offset] = s;
        }
        return active;
    }
}
