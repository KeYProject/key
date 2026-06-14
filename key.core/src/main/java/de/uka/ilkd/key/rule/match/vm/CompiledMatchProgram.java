/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ContextStatementBlock;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.ProgramChildrenMatcher;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchGenericSortInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchIdentityInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchInstructionForSV;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getSimilarParametricFunctionInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchAndBindVariables;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchModalOperatorSV;

/**
 * A compiled {@link MatchProgram} for a taclet's find expression. Instead of interpreting a list of
 * {@code VMInstruction}s over a generic {@code PoolSyntaxElementCursor}, it navigates the term
 * structure directly via {@code term.op()} / {@code term.sub(i)} (and the Java program via
 * {@code getChild(i)}), which avoids the cursor entirely.
 * <p>
 * It compiles essentially the whole taclet base: ordinary operators and schema variables, bound
 * variables (quantifiers / substitutions), modalities with their Java program (generic programs and
 * context blocks, see {@link #compileModality}), parametric function instances and elementary
 * updates. Program elements that define their own {@code match} (value literals, type references,
 * loops, ...) and generic elements with variable-arity children (a list schema variable
 * {@code #slist}) are reused cursor-free by {@linkplain #delegateToMatch delegating to their own
 * match}, so the surrounding term stays compiled. {@link #compile(JTerm)} returns {@code null} only
 * for the rare patterns it still cannot handle -- term labels, parametric-sort generic arguments,
 * unusual schema-variable shapes -- and the caller then falls back to the
 * {@code VMProgramInterpreter}, which stays the source of truth so the compiled path can always be
 * switched off.
 *
 * @see org.key_project.prover.rules.matcher.vm.VMProgramInterpreter
 */
public final class CompiledMatchProgram implements MatchProgram {

    /** number of find patterns that were successfully compiled (for measurement). */
    private static final AtomicLong COMPILED = new AtomicLong();
    /** number of find patterns that fell back to the interpreter (for measurement). */
    private static final AtomicLong FALLBACK = new AtomicLong();

    /**
     * A single compiled matching step over a (sub)term. Replaces the cursor-driven instruction
     * sequence by direct navigation.
     */
    @FunctionalInterface
    private interface Step {
        @Nullable
        MatchResultInfo match(JTerm term, MatchResultInfo mc, LogicServices services);
    }

    private final Step root;

    private CompiledMatchProgram(Step root) {
        this.root = root;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement toMatch, MatchResultInfo mc,
            LogicServices services) {
        return root.match((JTerm) toMatch, mc, services);
    }

    /**
     * Compiles the given find pattern, or returns {@code null} if it uses a feature not yet
     * supported by the compiler (the caller then uses the interpreter).
     *
     * @param pattern the find expression of the taclet
     * @return a compiled program, or {@code null} to fall back to the interpreter
     */
    public static @Nullable CompiledMatchProgram compile(JTerm pattern) {
        final Step root = compileStep(pattern);
        if (root == null) {
            FALLBACK.incrementAndGet();
            return null;
        }
        COMPILED.incrementAndGet();
        return new CompiledMatchProgram(root);
    }

    private static @Nullable Step compileStep(JTerm pattern) {
        // term labels are matched by a dedicated instruction; not yet compiled
        if (pattern.hasLabels()) {
            return null;
        }

        final Step core = compileCore(pattern);
        if (core == null) {
            return null;
        }

        final ImmutableArray<QuantifiableVariable> boundVars = pattern.boundVars();
        if (boundVars.isEmpty()) {
            return core;
        }

        // bound variables (quantifiers, substitutions, ...): bind the pattern's bound variables to
        // the source term's bound variables (renaming-aware), match the operator and subterms in
        // that scope, then unbind -- exactly as the interpreter does with
        // BindVariablesInstruction / UnbindVariablesInstruction, but cursor-free. The bind
        // instruction reads the source term's own bound variables from the element it is given.
        final MatchInstruction bind = matchAndBindVariables(boundVars);
        return (term, mc, services) -> {
            MatchResultInfo r = bind.match(term, mc, services);
            if (r == null) {
                return null;
            }
            r = core.match(term, r, services);
            if (r == null) {
                return null;
            }
            return ((MatchConditions) r).shrinkRenameTable();
        };
    }

    /**
     * Compiles the operator and subterms of {@code pattern} (without the bound-variable / label
     * handling, which {@link #compileStep} wraps around this). Returns {@code null} if a construct
     * is not yet supported.
     */
    private static @Nullable Step compileCore(JTerm pattern) {
        final Operator op = pattern.op();

        if (op instanceof SchemaVariable sv) {
            if (pattern.arity() != 0) {
                return null; // unusual schema-variable shape; let the interpreter handle it
            }
            // a schema variable matches the whole (sub)term; reuse the existing SV match logic,
            // which already accepts the element directly (no cursor needed)
            final MatchInstruction svInstr = getMatchInstructionForSV(sv);
            return (term, mc, services) -> svInstr.match(term, mc, services);
        }

        // a modality: compile the modal-operator kind, the Java program and the sub-formula(s)
        if (op instanceof Modality) {
            return compileModality(pattern);
        }

        // a parametric function instance: similar-base check + generic-argument matching + subterms
        if (op instanceof ParametricFunctionInstance) {
            return compileParametricFunction(pattern);
        }

        // an elementary update lhs := value: match the left-hand side then the value
        if (op instanceof ElementaryUpdate) {
            return compileElementaryUpdate(pattern);
        }

        final int arity = pattern.arity();
        if (arity == 0) {
            // a constant/leaf operator: faithful to MatchIdentityInstruction (reference equality)
            return (term, mc, services) -> term.op() == op ? mc : null;
        }

        final Step[] subs = new Step[arity];
        for (int i = 0; i < arity; i++) {
            final Step s = compileStep(pattern.sub(i));
            if (s == null) {
                return null;
            }
            subs[i] = s;
        }

        return (term, mc, services) -> {
            if (term.op() != op) {
                return null;
            }
            MatchResultInfo r = mc;
            for (int i = 0; i < subs.length; i++) {
                r = subs[i].match(term.sub(i), r, services);
                if (r == null) {
                    return null;
                }
            }
            return r;
        };
    }

    /**
     * Compiles an elementary update {@code lhs := value}: matches the left-hand side (a schema
     * variable, or a concrete location variable by identity) then the value subterm, mirroring the
     * generator's elementary-update case.
     */
    private static @Nullable Step compileElementaryUpdate(JTerm pattern) {
        final ElementaryUpdate elUp = (ElementaryUpdate) pattern.op();
        final MatchInstruction lhsMatcher;
        if (elUp.lhs() instanceof SchemaVariable sv) {
            lhsMatcher = getMatchInstructionForSV(sv);
        } else if (elUp.lhs() instanceof LocationVariable locVar) {
            lhsMatcher = getMatchIdentityInstruction(locVar);
        } else {
            return null; // unexpected left-hand side kind -> fall back
        }
        final Step valueStep = compileStep(pattern.sub(0));
        if (valueStep == null) {
            return null;
        }
        return (term, mc, services) -> {
            if (!(term.op() instanceof ElementaryUpdate actualElUp)) {
                return null;
            }
            final MatchResultInfo r = lhsMatcher.match(actualElUp.lhs(), mc, services);
            return r == null ? null : valueStep.match(term.sub(0), r, services);
        };
    }

    /**
     * Compiles a parametric function instance: a similar-base check on the operator, then the
     * generic arguments (generic sorts via {@link MatchGenericSortInstruction}, concrete arguments
     * by identity), then the subterms. Mirrors the generator's parametric-function case. Returns
     * {@code null} if a generic argument uses a parametric sort instance (which the generator does
     * not handle either).
     */
    private static @Nullable Step compileParametricFunction(JTerm pattern) {
        final ParametricFunctionInstance pfi = (ParametricFunctionInstance) pattern.op();
        final MatchInstruction similar = getSimilarParametricFunctionInstruction(pfi);

        final int argCount = pfi.getChildCount();
        final MatchInstruction[] argMatchers = new MatchInstruction[argCount];
        for (int i = 0; i < argCount; i++) {
            final GenericArgument arg = (GenericArgument) pfi.getChild(i);
            if (arg.sort() instanceof GenericSort gs) {
                argMatchers[i] = getMatchGenericSortInstruction(gs);
            } else if (arg.sort() instanceof ParametricSortInstance) {
                return null; // parametric sort in generic args: generator does not handle it either
            } else {
                argMatchers[i] = getMatchIdentityInstruction(arg);
            }
        }

        final int arity = pattern.arity();
        final Step[] subs = new Step[arity];
        for (int i = 0; i < arity; i++) {
            final Step s = compileStep(pattern.sub(i));
            if (s == null) {
                return null;
            }
            subs[i] = s;
        }

        return (term, mc, services) -> {
            if (!(term.op() instanceof ParametricFunctionInstance actualPfi)) {
                return null;
            }
            MatchResultInfo r = similar.match(actualPfi, mc, services);
            for (int i = 0; r != null && i < argCount; i++) {
                r = argMatchers[i].match(actualPfi.getChild(i), r, services);
            }
            for (int i = 0; r != null && i < subs.length; i++) {
                r = subs[i].match(term.sub(i), r, services);
            }
            return r;
        };
    }

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
     * Compiles a modality pattern {@code \<prog\> phi}: the modal-operator kind (reusing the
     * existing element-based instructions), the Java program (generic program or context block,
     * cursor-free) and the sub-formula(s). Returns {@code null} if the program or a sub-formula
     * uses
     * a construct the compiler does not handle (the caller then falls back to the interpreter).
     */
    private static @Nullable Step compileModality(JTerm pattern) {
        final Modality mod = (Modality) pattern.op();
        final MatchInstruction kindInstr =
            mod.kind() instanceof ModalOperatorSV sv ? matchModalOperatorSV(sv)
                    : getMatchIdentityInstruction(mod.kind());

        final JavaProgramElement prog = pattern.javaBlock().program();
        final Step progMatch;
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
                progMatch = (term, mc, services) -> csb.match(
                    new SourceData(term.javaBlock().program(), -1, (Services) services),
                    (MatchConditions) mc, phase3);
            } else {
                // an active statement is variable-arity (a list SV) or otherwise uncompilable:
                // delegate the whole context match to the interpreter (its matchChildren handles
                // list SVs); the surrounding term skeleton stays compiled
                progMatch = (term, mc, services) -> csb.match(
                    new SourceData(term.javaBlock().program(), -1, (Services) services),
                    (MatchConditions) mc);
            }
        } else {
            final ProgStep ps = compileProgram(prog);
            if (ps == null) {
                return null;
            }
            progMatch = (term, mc, services) -> ps.match(term.javaBlock().program(), mc, services);
        }

        final int arity = pattern.arity();
        final Step[] subs = new Step[arity];
        for (int i = 0; i < arity; i++) {
            final Step s = compileStep(pattern.sub(i));
            if (s == null) {
                return null;
            }
            subs[i] = s;
        }

        return (term, mc, services) -> {
            if (!(term.op() instanceof Modality m)) {
                return null;
            }
            MatchResultInfo r = kindInstr.match(m.kind(), mc, services);
            if (r == null) {
                return null;
            }
            r = progMatch.match(term, r, services);
            if (r == null) {
                return null;
            }
            for (int i = 0; i < subs.length; i++) {
                r = subs[i].match(term.sub(i), r, services);
                if (r == null) {
                    return null;
                }
            }
            return r;
        };
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

    /** @return {@code [compiled, fallback]} pattern counts since startup (for measurement). */
    public static long[] statistics() {
        return new long[] { COMPILED.get(), FALLBACK.get() };
    }
}
