/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

/**
 * The operator-specific "head" of an {@link OperatorPlan}: it checks the operator of a term and any
 * operator-specific data (e.g. a modal-operator kind, a parametric function's generic arguments,
 * an elementary update's left-hand side), but <em>not</em> the subterms -- those are recursed by
 * the enclosing {@link OperatorPlan}.
 *
 * <p>
 * Generic heads (ordinary operators) live in this module; language-specific heads (parametric
 * functions, updates, ...) are supplied by the front-end. A head carries both back-ends.
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
     * does not recurse into subterms.
     *
     * @return the compiled head matcher
     */
    MatchProgram compileHeadCheck();

    /**
     * The operator family this head accepts, as a key for indexing: two terms this head could
     * accept must yield equal descriptors, and a term whose top operator is of a different
     * family must yield a different one. A head that checks its operator by identity returns the
     * operator itself; a head that accepts a whole family (for example every instance of a
     * parametric function) returns the family's representative (its base). Returns {@code null}
     * if the head cannot be summarized by one family (for example a schematic modality kind,
     * which stands for several kinds at once); clients must then not index by this head.
     * <p>
     * This method is deliberately abstract: whoever adds a head for a new operator kind must
     * state its family here, next to the matching rule the family has to agree with. See
     * {@link MatchPlanBuilder#keySourceFor} for the consumer.
     *
     * @return the operator family descriptor, or {@code null} if there is none
     */
    @Nullable
    Object topOperatorDescriptor();
}
