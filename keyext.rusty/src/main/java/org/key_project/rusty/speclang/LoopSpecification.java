/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.LoopExpression;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;

/**
 * A loop invariant, consisting of an invariant formula, a set of loop predicates, a modifiable
 * clause, and a variant term.
 */
public interface LoopSpecification extends SpecificationElement {
    @Override
    LoopSpecification map(UnaryOperator<Term> op, Services services);

    /**
     * Returns the loop to which the invariant belongs.
     */
    LoopExpression getLoop();

    /**
     * Returns the contracted function symbol.
     */
    ProgramFunction getTarget();

    /**
     * Returns the invariant formula.
     *
     * @param services the Services object.
     * @return The invariant formula as a term.
     */
    Term getInvariant(Services services);

    /**
     * Returns the invariant formula.
     *
     * @param services the Services object.
     * @return The invariant formula as a term.
     */
    Term getInvariant(Map<ProgramVariable, Term> atPres, Services services);

    /**
     * Returns the variant term.
     *
     * @param services the Services object.
     * @return The variant term.
     */
    Term getVariant(Services services);

    /**
     * Returns the variant term.
     *
     * @param services the Services object.
     * @return The variant term.
     */
    Term getVariant(Map<ProgramVariable, Term> atPres, Services services);

    /**
     * Returns operators internally used for the pre-heap.
     *
     * @return The map storing the operators.
     */
    Map<ProgramVariable, Term> getInternalAtPres();

    LoopSpecification withInRangePredicates(Services services);
}
