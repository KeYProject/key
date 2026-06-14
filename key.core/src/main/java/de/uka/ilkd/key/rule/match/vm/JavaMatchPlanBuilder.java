/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.compiler.GenericOperatorHead;
import org.key_project.prover.rules.matcher.compiler.MatchHead;
import org.key_project.prover.rules.matcher.compiler.MatchPlan;
import org.key_project.prover.rules.matcher.compiler.OperatorPlan;
import org.key_project.prover.rules.matcher.compiler.SchemaVarPlan;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchInstructionForSV;

/**
 * The single Java-DL dispatch that builds a {@link MatchPlan} for a find pattern, from which both
 * the interpreter and the compiled find-matcher are derived. Describing a construct here gives both
 * back-ends at once (the goal of the match-plan framework).
 *
 * <p>
 * It covers the FOL term skeleton (schema variables, ordinary operators with their subterms, bound
 * variables), elementary updates, parametric function instances and modalities (the Java program is
 * matched through a {@link org.key_project.prover.rules.matcher.compiler.ProgramMatchHook}). It
 * returns {@code null} only for constructs outside this set (currently term labels) or when a
 * modality's program cannot be matched by the framework, so callers fall back to the legacy
 * hand-written matchers for those.
 */
public final class JavaMatchPlanBuilder {

    private JavaMatchPlanBuilder() {}

    /**
     * Builds the interpreter program for {@code pattern} through the match-plan framework, reading
     * the {@code key.matcher.programInstructions} flag (as the legacy generator does). Falls back
     * to
     * the legacy generator for constructs the framework does not build (term labels).
     *
     * @param pattern the find / assumes pattern
     * @return the VM instruction program
     */
    public static VMInstruction[] interpreterProgram(JTerm pattern) {
        return interpreterProgram(pattern,
            Boolean.getBoolean(SyntaxElementMatchProgramGenerator.PROGRAM_INSTRUCTIONS_PROPERTY));
    }

    /**
     * Builds the interpreter program for {@code pattern} through the match-plan framework, falling
     * back to the legacy generator for constructs the framework does not build (term labels).
     *
     * @param pattern the find / assumes pattern
     * @param programInstructions whether modality programs are converted to VM instructions
     * @return the VM instruction program
     */
    public static VMInstruction[] interpreterProgram(JTerm pattern, boolean programInstructions) {
        final MatchPlan plan = buildPlan(pattern, programInstructions);
        if (plan == null) {
            return SyntaxElementMatchProgramGenerator.createProgram(pattern, programInstructions);
        }
        final List<VMInstruction> out = new ArrayList<>();
        plan.emitInstructions(out);
        return out.toArray(new VMInstruction[0]);
    }

    /**
     * Builds the cursor-free compiled matcher for {@code pattern} through the match-plan framework,
     * falling back to the legacy compiled matcher for constructs the framework does not build.
     *
     * @param pattern the find pattern
     * @return the compiled matcher, or {@code null} if neither the framework nor the legacy
     *         compiler
     *         can build it (the caller then uses the interpreter)
     */
    public static @Nullable MatchProgram compiledProgram(JTerm pattern) {
        final MatchPlan plan = buildPlan(pattern, false);
        if (plan != null) {
            return plan.compile();
        }
        return CompiledMatchProgram.compile(pattern);
    }

    /**
     * Builds a match plan for {@code pattern}, or returns {@code null} if it uses a construct not
     * yet handled by the dispatch (the caller then uses the legacy matcher).
     *
     * @param pattern the find (sub)pattern
     * @param programInstructions whether modality programs are converted to VM instructions on the
     *        interpreter side (irrelevant for the FOL skeleton and the compiled back-end)
     * @return a match plan, or {@code null} to fall back
     */
    public static @Nullable MatchPlan buildPlan(JTerm pattern, boolean programInstructions) {
        if (pattern.hasLabels()) {
            return null; // term labels: not handled by the framework yet
        }
        final Operator op = pattern.op();

        if (op instanceof SchemaVariable sv) {
            if (pattern.arity() != 0) {
                return null; // unusual schema-variable shape
            }
            return new SchemaVarPlan(getMatchInstructionForSV(sv), pattern.boundVars(),
                JavaBinderMatcher.INSTANCE);
        }

        final MatchHead head = buildHead(pattern, programInstructions);
        if (head == null) {
            return null; // unsupported construct or uncompilable program -> fall back
        }

        // the operator head plus a plan per subterm
        final int arity = pattern.arity();
        final List<MatchPlan> children = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
            final MatchPlan child = buildPlan(pattern.sub(i), programInstructions);
            if (child == null) {
                return null; // a subterm is not handled -> the whole pattern falls back
            }
            children.add(child);
        }
        return new OperatorPlan(head, children, pattern.boundVars(), JavaBinderMatcher.INSTANCE);
    }

    /**
     * The operator-specific head for {@code pattern}'s operator, or {@code null} if the operator is
     * not supported (or, for a modality, its program cannot be matched by the framework).
     */
    private static @Nullable MatchHead buildHead(JTerm pattern, boolean programInstructions) {
        final Operator op = pattern.op();
        if (op instanceof ElementaryUpdate elUp) {
            return ElementaryUpdateHead.of(elUp);
        }
        if (op instanceof ParametricFunctionInstance pfi) {
            return ParametricFunctionHead.of(pfi);
        }
        if (op instanceof Modality mod) {
            return ModalityHead.of(mod, pattern.javaBlock().program(), programInstructions);
        }
        return new GenericOperatorHead(op);
    }
}
