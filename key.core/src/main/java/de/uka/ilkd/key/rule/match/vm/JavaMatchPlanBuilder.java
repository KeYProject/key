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
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.GenericOperatorHead;
import org.key_project.prover.rules.matcher.compiler.MatchHead;
import org.key_project.prover.rules.matcher.compiler.MatchPlan;
import org.key_project.prover.rules.matcher.compiler.OperatorPlan;
import org.key_project.prover.rules.matcher.compiler.SchemaVarPlan;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchInstructionForSV;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchTermLabelSV;

/**
 * The single Java-DL dispatch that builds a {@link MatchPlan} for a find pattern, from which both
 * the interpreter and the compiled find-matcher are derived. Describing a construct here gives both
 * back-ends at once -- this is the sole source of truth for find-matching; there is no separate
 * hand-written interpreter generator or compiled matcher to keep in sync.
 *
 * <p>
 * It covers the whole Java-DL find-taclet base: the FOL term skeleton (schema variables, ordinary
 * operators with their subterms, bound variables), term labels, elementary updates, parametric
 * function instances and modalities (the Java program is matched through a
 * {@link org.key_project.prover.rules.matcher.compiler.ProgramMatchHook}). A pattern the dispatch
 * genuinely cannot model yields {@code null} and the {@linkplain #interpreterProgram facades} raise
 * a clear error pointing at the missing head (no current taclet hits this; adding a construct means
 * adding one head, see the developer docs).
 */
public final class JavaMatchPlanBuilder {

    private JavaMatchPlanBuilder() {}

    /**
     * System property ({@code -Dkey.matcher.programInstructions=true}) selecting whether the Java
     * program of a modality is matched by a sub-program of {@link VMInstruction}s on the
     * interpreter back-end, instead of the monolithic {@code MatchProgramInstruction} (see
     * {@code SyntaxElementMatchProgramGenerator}). Default {@code false} keeps the existing
     * behaviour.
     * <p>
     * Read at matcher-construction time (i.e. when the taclet base is loaded) rather than once at
     * class load, so toggling it and reloading the proof switches the behaviour.
     */
    public static final String PROGRAM_INSTRUCTIONS_PROPERTY = "key.matcher.programInstructions";

    /**
     * Builds the interpreter program for {@code pattern} through the match-plan framework, reading
     * the {@code key.matcher.programInstructions} flag.
     *
     * @param pattern the find / assumes pattern
     * @return the VM instruction program
     */
    public static VMInstruction[] interpreterProgram(JTerm pattern) {
        return interpreterProgram(pattern, Boolean.getBoolean(PROGRAM_INSTRUCTIONS_PROPERTY));
    }

    /**
     * Builds the interpreter program for {@code pattern} through the match-plan framework.
     *
     * @param pattern the find / assumes pattern
     * @param programInstructions whether modality programs are converted to VM instructions
     * @return the VM instruction program
     */
    public static VMInstruction[] interpreterProgram(JTerm pattern, boolean programInstructions) {
        final List<VMInstruction> out = new ArrayList<>();
        planOrThrow(pattern, programInstructions).emit(out);
        return out.toArray(new VMInstruction[0]);
    }

    /**
     * Builds the cursor-free compiled matcher for {@code pattern} through the match-plan framework.
     *
     * @param pattern the find pattern
     * @return the compiled matcher
     */
    public static MatchProgram compiledProgram(JTerm pattern) {
        return planOrThrow(pattern, false).compile();
    }

    /**
     * Like {@link #compiledProgram(JTerm)}, but returns {@code null} instead of throwing when the
     * dispatch has no head for {@code pattern} (so the caller can fall back to the interpreter).
     * Used for {@code \assumes} formulas, which are not guaranteed to be among the patterns the
     * find-matcher coverage is validated against.
     *
     * @param pattern the find / assumes pattern
     * @return the compiled matcher, or {@code null} if the pattern is not compilable
     */
    public static @Nullable MatchProgram compiledProgramOrNull(JTerm pattern) {
        final MatchPlan plan = buildPlan(pattern, false);
        return plan == null ? null : plan.compile();
    }

    private static MatchPlan planOrThrow(JTerm pattern, boolean programInstructions) {
        final MatchPlan plan = buildPlan(pattern, programInstructions);
        if (plan == null) {
            throw new UnsupportedOperationException(
                "the match-plan framework has no head for this find pattern (op "
                    + pattern.op() + "); add one (see the taclet-matching developer docs): "
                    + pattern);
        }
        return plan;
    }

    /**
     * Builds a match plan for {@code pattern}, or returns {@code null} if it uses a construct the
     * dispatch cannot model (no current taclet does).
     *
     * @param pattern the find (sub)pattern
     * @param programInstructions whether modality programs are converted to VM instructions on the
     *        interpreter side (irrelevant for the FOL skeleton and the compiled back-end)
     * @return a match plan, or {@code null}
     */
    public static @Nullable MatchPlan buildPlan(JTerm pattern, boolean programInstructions) {
        final MatchPlan core = buildCore(pattern, programInstructions);
        if (core == null || !pattern.hasLabels()) {
            return core;
        }
        // term labels are matched in place (no cursor move), before the operator/subterms
        return new LabelPlan(matchTermLabelSV(pattern.getLabels()), core);
    }

    private static @Nullable MatchPlan buildCore(JTerm pattern, boolean programInstructions) {
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
            return null; // unsupported construct or uncompilable program
        }

        // the operator head plus a plan per subterm
        final int arity = pattern.arity();
        final List<MatchPlan> children = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
            final MatchPlan child = buildPlan(pattern.sub(i), programInstructions);
            if (child == null) {
                return null; // a subterm is not handled -> the whole pattern is unsupported
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

    /**
     * Wraps a plan with a term-label match: the labels are matched in place (the same
     * {@code matchTermLabelSV} instruction the interpreter uses, no cursor move) before the wrapped
     * operator/subterm matching. Reused by both back-ends.
     */
    private record LabelPlan(MatchInstruction labelInstr, MatchPlan inner) implements MatchPlan {
        @Override
        public void emit(List<VMInstruction> out) {
            out.add(labelInstr);
            inner.emit(out);
        }

        @Override
        public MatchProgram compile() {
            final MatchProgram innerCompiled = inner.compile();
            return (element, mc, services) -> {
                final MatchResultInfo r = labelInstr.match(element, mc, services);
                return r == null ? null : innerCompiled.match(element, r, services);
            };
        }
    }
}
