/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Optional;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Extracts the free loop invariants for the given loop term. Free invariants are only assumed, but
 * not proven (like an axiom).
 *
 * @author Dominic Steinhoefel
 */
public class LoopFreeInvariantCondition implements VariableCondition {
    private final ProgramSV loopStmtSV;
    private final SchemaVariable modalitySV;
    private final SchemaVariable invSV;

    public LoopFreeInvariantCondition(ProgramSV loopStmtSV, SchemaVariable modalitySV,
            SchemaVariable invSV) {
        this.loopStmtSV = loopStmtSV;
        this.modalitySV = modalitySV;
        this.invSV = invSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final TermBuilder tb = services.getTermBuilder();

        if (svInst.getInstantiation(invSV) != null) {
            return matchCond;
        }

        final LoopStatement loop = (LoopStatement) svInst.getInstantiation(loopStmtSV);
        final LoopSpecification loopSpec = services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }

        final JavaBlock javaBlock = JavaBlock.createJavaBlock(
            (StatementBlock) svInst.getContextInstantiation().contextProgram());

        final MethodFrame mf = //
            JavaTools.getInnermostMethodFrame(javaBlock, services);
        final Term selfTerm = Optional.ofNullable(mf)
                .map(methodFrame -> MiscTools.getSelfTerm(methodFrame, services)).orElse(null);

        final Modality modality = (Modality) svInst.getInstantiation(modalitySV);

        Term freeInvInst = tb.tt();
        for (final LocationVariable heap : MiscTools.applicableHeapContexts(modality, services)) {
            final Term currentFreeInvInst = freeInvInst;

            final Optional<Term> maybeFreeInvInst = Optional.ofNullable(
                loopSpec.getFreeInvariant(heap, selfTerm, loopSpec.getInternalAtPres(), services));

            freeInvInst =
                maybeFreeInvInst.map(inv -> tb.and(currentFreeInvInst, inv)).orElse(freeInvInst);
        }

        return matchCond.setInstantiations( //
            svInst.add(invSV, freeInvInst, services));
    }

    @Override
    public String toString() {
        return "\\getFreeInvariant(" + loopStmtSV + ", " + modalitySV + ", " + invSV + ")";
    }
}
