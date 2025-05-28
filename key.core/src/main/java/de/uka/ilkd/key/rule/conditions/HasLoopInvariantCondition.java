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
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchConditions;

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
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions matchCond, LogicServices p_services) {
        final Services services = (Services) p_services;
        final var svInst =
            (SVInstantiations) matchCond.getInstantiations();

        final LoopStatement loop = (LoopStatement) svInst.getInstantiation(loopStmtSV);
        final LoopSpecification loopSpec = //
            services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }

        final JavaBlock javaBlock = JavaBlock.createJavaBlock(
            (StatementBlock) svInst.getContextInstantiation().program());

        final MethodFrame mf = //
            JavaTools.getInnermostMethodFrame(javaBlock, services);
        final JTerm selfTerm = Optional.ofNullable(mf)
                .map(methodFrame -> MiscTools.getSelfTerm(methodFrame, services)).orElse(null);

        // TODO: handle exception!
        final JModality.JavaModalityKind modalityKind =
            (JModality.JavaModalityKind) svInst.getInstantiation(modalitySV);

        boolean hasInv = false;
        for (final LocationVariable heap : MiscTools.applicableHeapContexts(modalityKind,
            services)) {
            final Optional<JTerm> maybeInvInst = Optional.ofNullable(
                loopSpec.getInvariant(heap, selfTerm, loopSpec.getInternalAtPres(), services));
            final Optional<JTerm> maybeFreeInvInst = Optional.ofNullable(
                loopSpec.getFreeInvariant(heap, selfTerm, loopSpec.getInternalAtPres(), services));

            hasInv |= maybeInvInst.isPresent();
            hasInv |= maybeFreeInvInst.isPresent();
        }

        return hasInv ? matchCond : null;
    }

    @Override
    public String toString() {
        return "\\hasInvariant(" + loopStmtSV + "," + modalitySV + ")";
    }
}
