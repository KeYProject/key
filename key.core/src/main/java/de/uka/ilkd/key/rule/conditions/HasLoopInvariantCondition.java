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
 * Checks whether a loop has an invariant (either normal or "free").
 *
 * @author Dominic Steinhoefel
 */
public class HasLoopInvariantCondition implements VariableCondition {
    private final ProgramSV loopStmtSV;
    private final SchemaVariable modalitySV;

    public HasLoopInvariantCondition(ProgramSV loopStmtSV, SchemaVariable modalitySV) {
        this.loopStmtSV = loopStmtSV;
        this.modalitySV = modalitySV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        final LoopStatement loop = (LoopStatement) svInst.getInstantiation(loopStmtSV);
        final LoopSpecification loopSpec = //
            services.getSpecificationRepository().getLoopSpec(loop);

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

        boolean hasInv = false;
        for (final LocationVariable heap : MiscTools.applicableHeapContexts(modality, services)) {
            final Optional<Term> maybeInvInst = Optional.ofNullable(
                loopSpec.getInvariant(heap, selfTerm, loopSpec.getInternalAtPres(), services));
            final Optional<Term> maybeFreeInvInst = Optional.ofNullable(
                loopSpec.getFreeInvariant(heap, selfTerm, loopSpec.getInternalAtPres(), services));

            hasInv |= maybeInvInst.isPresent();
            hasInv |= maybeFreeInvInst.isPresent();
        }

        return hasInv ? matchCond : null;
    }

    @Override
    public String toString() {
        return "\\hasInvariant(" + loopStmtSV + ")";
    }
}
