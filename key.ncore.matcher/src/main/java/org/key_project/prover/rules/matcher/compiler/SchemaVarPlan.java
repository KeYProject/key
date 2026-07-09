/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextSiblingInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

/**
 * Plan for a (sub)pattern that is a schema variable: it matches the whole element via the provided
 * schema-variable {@link MatchInstruction} (which the front-end supplies, since schema-variable
 * kinds are language-specific). Bound variables, if any, are bound around it via the
 * {@link BinderMatcher}.
 *
 * <p>
 * Language-agnostic counterpart of the schema-variable branch of the hand-written matchers: the
 * interpreter emission is {@code matchSV + gotoNextSibling} (wrapped in bind/unbind), the compiled
 * emission applies the schema-variable instruction directly (wrapped in bind/unbind).
 */
public final class SchemaVarPlan implements MatchPlan {

    private final MatchInstruction schemaVarInstruction;
    private final ImmutableArray<? extends QuantifiableVariable> boundVars;
    private final BinderMatcher binder;

    public SchemaVarPlan(MatchInstruction schemaVarInstruction,
            ImmutableArray<? extends QuantifiableVariable> boundVars, BinderMatcher binder) {
        this.schemaVarInstruction = schemaVarInstruction;
        this.boundVars = boundVars;
        this.binder = binder;
    }

    @Override
    public void emitInstructions(List<VMInstruction> out) {
        // The schema-variable instruction matches the whole term at the term node and the sibling
        // advance skips its entire subtree, bound variables included -- the cursor never descends
        // here. So, unlike OperatorPlan (whose cursor walks the term's children), no per-bound-var
        // skips are emitted: they would move the cursor at the SIBLING level, past elements that
        // do not belong to this pattern.
        final boolean bound = !boundVars.isEmpty();
        if (bound) {
            out.add(binder.binder(boundVars));
        }
        out.add(schemaVarInstruction);
        out.add(GotoNextSiblingInstruction.INSTANCE);
        if (bound) {
            out.add(binder.unbinderInstruction());
        }
    }

    @Override
    public MatchProgram compile() {
        final MatchInstruction sv = schemaVarInstruction;
        final MatchProgram core = sv::match;
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
            return body == null ? null : binder.unbind(body);
        };
    }
}
