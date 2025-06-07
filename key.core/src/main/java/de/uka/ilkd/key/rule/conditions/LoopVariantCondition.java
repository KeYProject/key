/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

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
    public MatchResultInfo check(SchemaVariable var, SyntaxElement instCandidate,
            MatchResultInfo matchCond, LogicServices p_services) {
        final var svInst = matchCond.getInstantiations();
        final var services = (Services) p_services;

        if (svInst.getInstantiation(variantSV) != null) {
            return matchCond;
        }

        final LoopStatement loop = (LoopStatement) svInst.getInstantiation(loopStmtSV);
        final LoopSpecification loopSpec = services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }
        final JTerm variant = loopSpec.getVariant(loopSpec.getInternalSelfTerm(),
            loopSpec.getInternalAtPres(), services);

        if (variant == null) {
            return null;
        }

        return matchCond.setInstantiations(//
            ((SVInstantiations) svInst).add(variantSV, variant,
                services));
    }

    @Override
    public String toString() {
        return "\\getVariant(" + loopStmtSV + ", " + variantSV + ")";
    }
}
