/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.InfiniteLoopExpression;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.VariableCondition;

/**
 * Extracts the variant for a loop term.
 *
 * @author Dominic Steinhoefel
 */
public class LoopVariantCondition implements VariableCondition {
    private final SchemaVariable loopExprSV;
    private final SchemaVariable variantSV;

    public LoopVariantCondition(ProgramSV loopExprSV, SchemaVariable variantSV) {
        this.loopExprSV = loopExprSV;
        this.variantSV = variantSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions matchCond, Services services) {
        final var svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(variantSV) != null) {
            return matchCond;
        }

        final var loop = (InfiniteLoopExpression) svInst.getInstantiation(loopExprSV);
        final var loopSpec = services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }
        final Term variant = loopSpec.getVariant(services);

        if (variant == null) {
            return null;
        }

        return matchCond.setInstantiations(svInst.add(variantSV, variant, services));
    }
}
