/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.Path;
import org.key_project.rusty.ast.PathSegment;
import org.key_project.rusty.ast.ResDef;
import org.key_project.rusty.ast.expr.AssignmentExpression;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.expr.CallExpression;
import org.key_project.rusty.ast.expr.PathExpr;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.speclang.FunctionalOperationContract;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * <p>
 * The proof obligation for operation contracts.
 * </p>
 * <p>
 * The generated {@link Sequent} has the following form:
 *
 * <pre>
 * {@code
 * ==>
 * <generalAssumptions> &
 * <preconditions>
 * ->
 * <updatesToStoreInitialValues>
 * <modalityStart>
 * exc=null;try {<methodBodyExpand>}catch(java.lang.Throwable e) {exc = e}
 * <modalityEnd>
 * (exc = null & <postconditions > & <optionalUninterpretedPredicate>)
 * }
 * </pre>
 * </p>
 */
public class FunctionalOperationContractPO extends AbstractOperationPO implements ContractPO {
    private final FunctionalOperationContract contract;
    private Term mbyAtPre;

    public FunctionalOperationContractPO(InitConfig initConfig,
            FunctionalOperationContract contract) {
        super(initConfig, new Name(contract.getName()));
        this.contract = contract;
    }


    @Override
    protected ProgramFunction getProgramFunction() {
        return getContract().getTarget();
    }

    @Override
    protected Modality.RustyModalityKind getTerminationMarker() {
        return getContract().getModalityKind();
    }

    @Override
    protected Term getPre(ImmutableList<ProgramVariable> paramVars, Services proofServices) {
        final Term freePre = contract.getFreePre(null, paramVars, proofServices);
        final Term pre = contract.getPre(null, paramVars, proofServices);
        return freePre != null ? tb.and(pre, freePre) : pre;
    }

    @Override
    protected Term generateMbyAtPreDef(ImmutableList<ProgramVariable> paramVars,
            Services services) {
        final Term mbyAtPreDef;
        if (contract.hasMby()) {
            final Term mby = contract.getMby(null, paramVars, services);
            mbyAtPreDef = tb.measuredBy(mby);
        } else {
            mbyAtPreDef = tb.measuredByEmpty();
        }
        return mbyAtPreDef;
    }

    @Override
    protected Term getPost(ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            Services proofServices) {
        return contract.getPost(null, paramVars, resultVar, proofServices);
    }

    @Override
    protected BlockExpression buildOperationBlock(ImmutableList<ProgramVariable> formalParamVars,
            ProgramVariable resultVar, Services proofServices) {
        ProgramFunction target = contract.getTarget();
        var callee = new PathExpr(new Path<>(new ResDef(target), new ImmutableArray<>(
            new PathSegment(target.getFunction().name().toString(),
                new ResDef(target)))),
            target.getType().getRustyType());
        return new BlockExpression(ImmutableList.of(
            new ExpressionStatement(
                new AssignmentExpression(resultVar,
                    new CallExpression(callee, new ImmutableArray<>(formalParamVars.toList()))),
                true)),
            null);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public FunctionalOperationContract getContract() {
        return contract;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getMbyAtPre() {
        return mbyAtPre;
    }
}
