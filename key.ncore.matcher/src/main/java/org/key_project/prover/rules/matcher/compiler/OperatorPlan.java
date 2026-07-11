/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.CheckNodeKindInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextSiblingInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

/**
 * Plan for a term whose top operator is matched by a {@link MatchHead} (the operator + any
 * operator-specific data) and whose subterms are matched by child plans. Bound variables, if any,
 * are bound around the whole node via the {@link BinderMatcher}.
 *
 * <p>
 * The interpreter emission is {@code checkNodeKind(Term) + gotoNext + head +
 * (skip bound variables) + subterms}; the compiled matcher checks the head and then recurses into
 * the subterms. When the term binds variables, both back-ends wrap this in bind/unbind.
 */
public final class OperatorPlan implements MatchPlan {

    private final MatchHead head;
    private final List<MatchPlan> children;
    private final ImmutableArray<? extends QuantifiableVariable> boundVars;
    private final BinderMatcher binder;

    /**
     * @param head the operator head (operator + operator-specific checks)
     * @param children one plan per subterm, in order
     * @param boundVars the term's bound variables (possibly empty)
     * @param binder the binder SPI (used only if {@code boundVars} is non-empty)
     */
    public OperatorPlan(MatchHead head, List<MatchPlan> children,
            ImmutableArray<? extends QuantifiableVariable> boundVars, BinderMatcher binder) {
        this.head = head;
        this.children = children;
        this.boundVars = boundVars;
        this.binder = binder;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        final boolean bound = !boundVars.isEmpty();
        if (bound) {
            out.add(binder.binder(boundVars));
        }
        out.add(new CheckNodeKindInstruction(Term.class));
        out.add(GotoNextInstruction.INSTANCE);
        head.emit(out);
        if (bound) {
            // the cursor is inside the term (the head advanced past the operator): step over the
            // bound-variable children to reach the first subterm
            for (int i = 0, n = boundVars.size(); i < n; i++) {
                out.add(GotoNextSiblingInstruction.INSTANCE);
            }
        }
        for (MatchPlan child : children) {
            child.emit(out);
        }
        if (bound) {
            out.add(new UnbindInstruction(binder, boundVars));
        }
    }

    @Override
    public MatchProgram compile() {
        final MatchProgram headCheck = head.compileHeadCheck();
        final int n = children.size();
        final MatchProgram[] childMatchers = new MatchProgram[n];
        for (int i = 0; i < n; i++) {
            childMatchers[i] = children.get(i).compile();
        }
        final MatchProgram core = (element, mc, services) -> {
            MatchResultInfo r = headCheck.match(element, mc, services);
            if (r == null) {
                return null;
            }
            final Term term = (Term) element;
            for (int i = 0; i < n; i++) {
                r = childMatchers[i].match(term.sub(i), r, services);
                if (r == null) {
                    return null;
                }
            }
            return r;
        };
        if (boundVars.isEmpty()) {
            return core;
        }
        final MatchInstruction bind = binder.binder(boundVars);
        return (element, mc, services) -> {
            final @Nullable MatchResultInfo bound = bind.match(element, mc, services);
            if (bound == null) {
                return null;
            }
            final @Nullable MatchResultInfo body = core.match(element, bound, services);
            return body == null ? null : binder.unbind(body, boundVars);
        };
    }

    /**
     * The interpreter form of {@link BinderMatcher#unbind}: it closes the binding scope and
     * leaves the cursor untouched. It is a plain cursor-level instruction (not a
     * {@link MatchInstruction}) because it runs after the binder term's subterms have been
     * matched, when the cursor has already advanced past the whole term — there is no current
     * element it could read.
     */
    private record UnbindInstruction(BinderMatcher binder,
            ImmutableArray<? extends QuantifiableVariable> boundVars) implements VMInstruction {
        @Override
        public MatchResultInfo match(PoolSyntaxElementCursor cursor, MatchResultInfo mc,
                LogicServices services) {
            return binder.unbind(mc, boundVars);
        }
    }

    @Override
    public String toString() {
        return "term(" + head + (boundVars.isEmpty() ? "" : ", bind " + boundVars)
            + (children.isEmpty() ? "" : ", " + children) + ")";
    }
}
