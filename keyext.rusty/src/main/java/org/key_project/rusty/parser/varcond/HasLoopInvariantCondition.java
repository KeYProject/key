/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.InfiniteLoopExpression;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.VariableCondition;
import org.key_project.rusty.speclang.LoopSpecification;

/**
 * Checks whether a loop has an invariant.
 *
 * @author Dominic Steinhoefel
 */
public class HasLoopInvariantCondition implements VariableCondition {
    private final ProgramSV loopExprSV;
    private final SchemaVariable modalitySV;

    public HasLoopInvariantCondition(ProgramSV loopExprSV, SchemaVariable modalitySV) {
        this.loopExprSV = loopExprSV;
        this.modalitySV = modalitySV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions matchCond, Services services) {
        final var svInst = matchCond.getInstantiations();

        final var loop = (InfiniteLoopExpression) svInst.getInstantiation(loopExprSV);
        final LoopSpecification loopSpec = services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }

        final var rb = new RustyBlock(svInst.getContextInstantiation().contextProgram());

        var modKind = (Modality.RustyModalityKind) svInst.getInstantiation(modalitySV);

        return loopSpec.getInvariant(services) != null ? matchCond : null;
    }

    @Override
    public String toString() {
        return "\\hasInvariant(" + loopExprSV + "," + modalitySV + ")";
    }
}
