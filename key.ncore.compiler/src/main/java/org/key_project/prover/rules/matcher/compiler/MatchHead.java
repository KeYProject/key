/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * The operator-specific "head" of an {@link OperatorPlan}: it checks the operator of a term and any
 * operator-specific data (e.g. a modal-operator kind, a parametric function's generic arguments,
 * an elementary update's left-hand side), but <em>not</em> the subterms -- those are recursed by
 * the
 * enclosing {@link OperatorPlan}.
 *
 * <p>
 * Generic heads (ordinary operators) live in this module; language-specific heads (modalities,
 * parametric functions, ...) are supplied by the front-end. A head carries both back-ends, lifted
 * from the corresponding hand-written matcher fragments.
 */
public interface MatchHead {

    /**
     * Appends the interpreter instructions matching this head. On entry the cursor points at the
     * operator; on completion it must point at the first subterm so the enclosing
     * {@link OperatorPlan} can match the subterms.
     *
     * @param out the instruction list being built
     */
    void emit(List<VMInstruction> out);

    /**
     * Builds the compiled head check: applied to the term element, it verifies the operator (and
     * head-specific data) and returns the extended match result, or {@code null} on failure. It
     * does
     * not recurse into subterms.
     *
     * @return the compiled head matcher
     */
    MatchProgram compileHeadCheck();
}
