/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * Extracts the variant for a loop term.
 *
 * @author Dominic Steinhoefel
 */
public class LoopVariantCondition implements VariableCondition {
    private final SchemaVariable loopStmtSV;
    private final SchemaVariable variantSV;

    public LoopVariantCondition(ProgramSV loopStmtSV, SchemaVariable variantSV) {
        this.loopStmtSV = loopStmtSV;
        this.variantSV = variantSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(variantSV) != null) {
            return matchCond;
        }

        final LoopStatement loop = (LoopStatement) svInst.getInstantiation(loopStmtSV);
        final LoopSpecification loopSpec = services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }
        final Term variant = loopSpec.getVariant(loopSpec.getInternalSelfTerm(),
            loopSpec.getInternalAtPres(), services);

        if (variant == null) {
            return null;
        }

        return matchCond.setInstantiations(//
            svInst.add(variantSV, variant, services));
    }

    @Override
    public String toString() {
        return "\\getVariant(" + loopStmtSV + ", " + variantSV + ")";
    }
}
