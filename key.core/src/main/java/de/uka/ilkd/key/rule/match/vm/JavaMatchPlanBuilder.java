/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.BinderMatcher;
import org.key_project.prover.rules.matcher.compiler.GenericOperatorHead;
import org.key_project.prover.rules.matcher.compiler.MatchHead;
import org.key_project.prover.rules.matcher.compiler.MatchPlan;
import org.key_project.prover.rules.matcher.compiler.MatchPlanBuilder;
import org.key_project.prover.rules.matcher.compiler.ModalityHead;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchIdentityInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchInstructionForSV;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchModalOperatorSV;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchTermLabelSV;

/**
 * The Java-DL front-end of the term-side {@link MatchPlanBuilder}: it supplies the Java-DL
 * schema-variable instructions, the per-operator head dispatch, the {@link JavaBinderMatcher} and
 * the term-label wrap; the recursion over the pattern and the derivation of both back-ends are
 * inherited from the framework. Describing a construct here gives both back-ends at once -- this
 * is the sole source of truth for find-matching; there is no separate hand-written interpreter
 * generator or compiled matcher to keep in sync.
 *
 * <p>
 * The dispatch covers the whole Java-DL find-taclet base: the FOL term skeleton (schema variables,
 * ordinary operators with their subterms, bound variables), term labels, elementary updates,
 * parametric function instances and modalities (the Java program is matched through a
 * {@link org.key_project.prover.rules.matcher.compiler.ProgramMatchHook}). A pattern the dispatch
 * genuinely cannot model yields {@code null} and the {@linkplain #interpreterProgram(JTerm)
 * facades} raise a clear error pointing at the missing head (no current taclet hits this; adding a
 * construct means adding one head, see the developer docs).
 */
public final class JavaMatchPlanBuilder extends MatchPlanBuilder {

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

    /** the dispatch whose interpreter emission converts modality programs to VM instructions. */
    private static final JavaMatchPlanBuilder CONVERTING = new JavaMatchPlanBuilder(true);
    /** the dispatch whose interpreter emission matches modality programs monolithically. */
    private static final JavaMatchPlanBuilder DELEGATING = new JavaMatchPlanBuilder(false);

    /** whether modality programs are converted to VM instructions on the interpreter side. */
    private final boolean programInstructions;

    private JavaMatchPlanBuilder(boolean programInstructions) {
        this.programInstructions = programInstructions;
    }

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
        // the (Term) view selects the inherited instance method, not this static facade
        return (programInstructions ? CONVERTING : DELEGATING)
                .interpreterProgram((Term) pattern);
    }

    /**
     * Builds the cursor-free compiled matcher for {@code pattern} through the match-plan
     * framework.
     *
     * @param pattern the find pattern
     * @return the compiled matcher
     */
    public static MatchProgram compiledProgram(JTerm pattern) {
        return DELEGATING.compiledProgram((Term) pattern);
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
        return DELEGATING.compiledProgramOrNull((Term) pattern);
    }

    @Override
    protected MatchInstruction instructionForSV(SchemaVariable sv) {
        return getMatchInstructionForSV(sv);
    }

    /**
     * The operator-specific head for {@code pattern}'s operator, or {@code null} if the operator
     * is not supported (or, for a modality, its program cannot be matched by the framework).
     */
    @Override
    protected @Nullable MatchHead headFor(Term pattern) {
        final Operator op = pattern.op();
        if (op instanceof ElementaryUpdate elUp) {
            return ElementaryUpdateHead.of(elUp);
        }
        if (op instanceof ParametricFunctionInstance pfi) {
            return ParametricFunctionHead.of(pfi);
        }
        if (op instanceof Modality mod) {
            final JavaProgramMatchHook hook = JavaProgramMatchHook
                    .of(((JTerm) pattern).javaBlock().program(), programInstructions);
            if (hook == null) {
                return null; // the modality's program cannot be matched by the framework
            }
            final MatchInstruction kindInstr = mod.kind() instanceof ModalOperatorSV sv
                    ? matchModalOperatorSV(sv)
                    : getMatchIdentityInstruction(mod.kind());
            return new ModalityHead(mod.kind(), kindInstr, hook);
        }
        return new GenericOperatorHead(op);
    }

    @Override
    protected BinderMatcher binder() {
        return JavaBinderMatcher.INSTANCE;
    }

    @Override
    protected MatchPlan finishPlan(Term pattern, MatchPlan core) {
        final JTerm jPattern = (JTerm) pattern;
        if (!jPattern.hasLabels()) {
            return core;
        }
        // term labels are matched in place (no cursor move), before the operator/subterms
        return new LabelPlan(matchTermLabelSV(jPattern.getLabels()), core);
    }

    /**
     * Wraps a plan with a term-label match: the labels are matched in place (the same
     * {@code matchTermLabelSV} instruction the interpreter uses, no cursor move) before the
     * wrapped operator/subterm matching. Reused by both back-ends.
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
