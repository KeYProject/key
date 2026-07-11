/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.util.collection.ImmutableArray;

/**
 * Language SPI for matching <em>bound variables</em> (the variables introduced by a binder such as
 * a quantifier, a substitution or a {@code let}). Binding is language-specific: each front-end
 * binds its own kinds of logic and schema variables and keeps its own renaming/instantiation
 * state.
 *
 * <p>
 * The match-plan framework owns the <em>scaffolding</em> (bind the pattern's bound variables before
 * matching the operator and subterms, then unbind afterwards, in both back-ends); a language plugs
 * in the actual binding behaviour here. The {@linkplain #binder(ImmutableArray) binder} matches the
 * pattern's bound variables against the source element's own bound variables and is shared by both
 * back-ends (it is element-based); only the un-binding is back-end specific (an instruction for the
 * interpreter, a direct call for the compiler).
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
     * The interpreter instruction that pops the binding scope opened by {@link #binder}.
     *
     * @return the un-binding instruction
     */
    VMInstruction unbinderInstruction();

    /**
     * Pops the binding scope opened by {@link #binder} for the compiled back-end.
     *
     * @param mc the match result after matching the binder body
     * @return the match result with the binding scope removed
     */
    MatchResultInfo unbind(MatchResultInfo mc);
}
