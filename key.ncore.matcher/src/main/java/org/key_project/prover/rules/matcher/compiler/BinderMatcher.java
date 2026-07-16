/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.util.collection.ImmutableArray;

/**
 * Language SPI (service provider interface) for matching <em>bound variables</em> (the variables
 * introduced by a binder such as
 * a quantifier, a substitution or a {@code let}). Binding is language-specific: each front-end
 * binds its own kinds of logic and schema variables and keeps its own binding state, for example
 * a renaming table with nested scopes, or a counted stack of the variables bound along the current
 * path.
 *
 * <p>
 * The match-plan framework owns the <em>scaffolding</em>: it binds the pattern's bound variables
 * before matching the operator and subterms and unbinds them afterwards, on both back-ends. A
 * language plugs in the two operations here. The {@linkplain #binder(ImmutableArray) binder} is an
 * element-based instruction (it reads the source element's own bound variables), so both back-ends
 * apply it as it is; {@link #unbind} reads no element at all (it only transforms the match
 * state), so the framework calls it directly on the compiled back-end and wraps it into a
 * cursor-neutral instruction for the interpreter.
 */
public interface BinderMatcher {

    /**
     * The element-based instruction that binds the given pattern bound variables (it reads the
     * source element's own bound variables). Used by both back-ends.
     *
     * @param boundVars the pattern's bound variables
     * @return the binding instruction
     */
    MatchInstruction binder(ImmutableArray<? extends QuantifiableVariable> boundVars);

    /**
     * Closes the binding scope opened by {@link #binder} for the same variables. A front-end
     * whose binding state is scope-structured pops one scope and may ignore {@code boundVars};
     * one that keeps a counted stack pops {@code boundVars.size()} entries.
     *
     * @param mc the match result after matching the binder's body
     * @param boundVars the pattern bound variables the scope was opened for
     * @return the match result with the binding scope closed
     */
    MatchResultInfo unbind(MatchResultInfo mc,
            ImmutableArray<? extends QuantifiableVariable> boundVars);
}
