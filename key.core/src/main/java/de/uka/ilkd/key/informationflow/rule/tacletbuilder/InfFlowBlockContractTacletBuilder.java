/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public final class InfFlowBlockContractTacletBuilder
        extends AbstractInfFlowContractAppTacletBuilder {

    private BlockContract blockContract;
    private ExecutionContext executionContext;


    public InfFlowBlockContractTacletBuilder(final Services services) {
        super(services);
    }


    public void setContract(BlockContract contract) {
        this.blockContract = contract;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    @Override
    Name generateName() {
        return MiscTools.toValidTacletName(USE_IF + blockContract.getUniqueName());
    }

    @Override
    Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes, Services services) {
        BasicPOSnippetFactory fAssumes = POSnippetFactory.getBasicFactory(blockContract,
            schemaDataAssumes, executionContext, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    Term generateSchemaFind(ProofObligationVars schemaDataFind, Services services) {
        BasicPOSnippetFactory fFind = POSnippetFactory.getBasicFactory(blockContract,
            schemaDataFind, executionContext, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    Term getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
            POSnippetFactory.getBasicFactory(blockContract, appData, executionContext, services);
        return f.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    Term buildContractApplications(ProofObligationVars contAppData,
            ProofObligationVars contAppData2, Services services) {
        ImmutableSet<BlockContract> ifContracts =
            services.getSpecificationRepository().getBlockContracts(blockContract.getBlock());
        ifContracts = filterContracts(ifContracts);
        ImmutableList<Term> contractsApplications = ImmutableSLList.nil();
        for (BlockContract cont : ifContracts) {
            InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(cont, contAppData,
                contAppData2, executionContext, services);
            contractsApplications = contractsApplications
                    .append(f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APPL));
        }

        return and(contractsApplications);
    }


    ImmutableSet<BlockContract> filterContracts(ImmutableSet<BlockContract> ifContracts) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        for (BlockContract cont : ifContracts) {
            if ((cont.getBlock().getStartPosition().line() == blockContract.getBlock()
                    .getStartPosition().line())
                    && cont.getTarget().getUniqueName()
                            .equalsIgnoreCase(blockContract.getTarget().getUniqueName())) {
                result = result.add(cont);
            }
        }
        return result;
    }
}
