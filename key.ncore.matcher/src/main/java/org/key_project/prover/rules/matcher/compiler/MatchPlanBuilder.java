/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.ArrayList;
import java.util.List;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

/**
 * The language-agnostic skeleton of a term-side match-plan dispatch: it walks a find pattern
 * ({@link Term}: operator, subterms, bound variables) and composes the {@link MatchPlan} nodes
 * from which both matcher back-ends are derived. A language front-end subclasses it and supplies
 * only the per-language decisions:
 * <ul>
 * <li>{@link #instructionForSV(SchemaVariable)} — the match instruction for each of its
 * schema-variable kinds;</li>
 * <li>{@link #headFor(Term)} — the {@link MatchHead} for each operator: an operator-specific head
 * where its calculus has special matching (modalities, updates, ...), the
 * {@link GenericOperatorHead} for every ordinary operator, or {@code null} for a construct it
 * cannot model;</li>
 * <li>{@link #binder()} — its {@link BinderMatcher}, i.e. how bound variables are bound and
 * unbound;</li>
 * <li>optionally {@link #finishPlan(Term, MatchPlan)} — a hook to wrap the built plan with
 * language-specific in-place checks (for example term labels).</li>
 * </ul>
 * Everything else — the recursion over the pattern, the derivation of the interpreter program and
 * the compiled matcher, and the fail-at-load contract of {@link #planOrThrow(Term)} — is shared.
 *
 * <p>
 * A builder instance is stateless apart from what the subclass adds, so one instance is typically
 * shared for all patterns.
 */
public abstract class MatchPlanBuilder {

    /**
     * The match instruction for a schema-variable pattern. Schema-variable kinds (term, formula,
     * variable, program, ...) and how their instantiations are recorded are language-specific, so
     * the front-end supplies the instruction; the framework only places it in the plan.
     *
     * @param sv the pattern's schema variable
     * @return the instruction matching {@code sv} against a source element
     */
    protected abstract MatchInstruction instructionForSV(SchemaVariable sv);

    /**
     * The operator-specific {@link MatchHead} for {@code pattern}'s operator: the front-end's
     * dispatch. It returns a special head where the calculus has special matching, a
     * {@link GenericOperatorHead} for an ordinary operator, or {@code null} if the construct
     * cannot be modelled (the pattern is then unsupported as a whole).
     *
     * @param pattern the find (sub)pattern whose operator is dispatched on
     * @return the head, or {@code null} if the operator is unsupported
     */
    protected abstract @Nullable MatchHead headFor(Term pattern);

    /**
     * The language's {@link BinderMatcher}, used for every pattern that binds variables.
     *
     * @return the language's {@link BinderMatcher}
     */
    protected abstract BinderMatcher binder();

    /**
     * Hook to wrap the plan built for {@code pattern} with language-specific in-place checks that
     * precede the operator match (for example term labels). The default returns the plan
     * unchanged.
     *
     * @param pattern the find (sub)pattern the plan was built for
     * @param core the plan built by the framework
     * @return the plan to use for {@code pattern}
     */
    protected MatchPlan finishPlan(Term pattern, MatchPlan core) {
        return core;
    }

    /**
     * Builds the interpreter program for {@code pattern} through the match-plan framework.
     *
     * @param pattern the find / assumes pattern
     * @return the VM instruction program
     */
    public final VMInstruction[] interpreterProgram(Term pattern) {
        final List<VMInstruction> out = new ArrayList<>();
        planOrThrow(pattern).emit(out);
        return out.toArray(new VMInstruction[0]);
    }

    /**
     * Builds the cursor-free compiled matcher for {@code pattern} through the match-plan
     * framework.
     *
     * @param pattern the find pattern
     * @return the compiled matcher
     */
    public final MatchProgram compiledProgram(Term pattern) {
        return planOrThrow(pattern).compile();
    }

    /**
     * Like {@link #compiledProgram(Term)}, but returns {@code null} instead of throwing when the
     * dispatch has no head for {@code pattern} (so the caller can fall back to the interpreter).
     * Used for {@code \assumes} formulas, which are not guaranteed to be among the patterns the
     * find-matcher coverage is validated against.
     *
     * @param pattern the find / assumes pattern
     * @return the compiled matcher, or {@code null} if the pattern is not compilable
     */
    public final @Nullable MatchProgram compiledProgramOrNull(Term pattern) {
        final MatchPlan plan = buildPlan(pattern);
        return plan == null ? null : plan.compile();
    }

    /**
     * Builds the match plan for {@code pattern}, or fails with a clear error naming the
     * unsupported operator. The failure happens at taclet-load time, so an unsupported construct
     * is reported when the rule is loaded, not silently mis-matched during proof search.
     *
     * @param pattern the find / assumes pattern
     * @return the match plan
     */
    public final MatchPlan planOrThrow(Term pattern) {
        final MatchPlan plan = buildPlan(pattern);
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
     * front-end's dispatch cannot model.
     *
     * @param pattern the find (sub)pattern
     * @return a match plan, or {@code null}
     */
    public final @Nullable MatchPlan buildPlan(Term pattern) {
        final MatchPlan core = buildCore(pattern);
        return core == null ? core : finishPlan(pattern, core);
    }

    private @Nullable MatchPlan buildCore(Term pattern) {
        final Operator op = pattern.op();

        if (op instanceof SchemaVariable sv) {
            if (pattern.arity() != 0 || !pattern.boundVars().isEmpty()) {
                // unusual schema-variable shape: no taclet produces these (bound variables attach
                // to binder operators, not schema variables) -- fall back with a clear error
                return null;
            }
            return new SchemaVarPlan(instructionForSV(sv));
        }

        final MatchHead head = headFor(pattern);
        if (head == null) {
            return null; // unsupported construct
        }

        // the operator head plus a plan per subterm
        final int arity = pattern.arity();
        final List<MatchPlan> children = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
            final MatchPlan child = buildPlan(pattern.sub(i));
            if (child == null) {
                return null; // a subterm is not handled -> the whole pattern is unsupported
            }
            children.add(child);
        }
        return new OperatorPlan(head, children, pattern.boundVars(), binder());
    }
}
