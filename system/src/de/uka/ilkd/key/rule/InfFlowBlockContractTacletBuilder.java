// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public final class InfFlowBlockContractTacletBuilder
        extends AbstractInfFlowContractTacletBuilder {

    private BlockContract blockContract;


    public InfFlowBlockContractTacletBuilder(final Services services) {
        super(services);
    }


    public void setContract(BlockContract contract) {
        this.blockContract = contract;
    }


    @Override
    Name generateName() {
        return MiscTools.toValidTacletName("Use information flow contract for " +
                                           blockContract.getName() + " " +
                                           blockContract.getBlock().getStartPosition().getLine() + " : " +
                                           blockContract.getTarget().getFullName());
    }


    @Override
    Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                               Services services) {
        BasicPOSnippetFactory fAssumes =
                POSnippetFactory.getBasicFactory(blockContract, schemaDataAssumes, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    Term generateSchemaFind(ProofObligationVars schemaDataFind,
                            Services services) {
        BasicPOSnippetFactory fFind =
                POSnippetFactory.getBasicFactory(blockContract, schemaDataFind, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    Term getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
                POSnippetFactory.getBasicFactory(blockContract, appData,
                                                 services);
        return f.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    Term buildContractApplications(
            ProofObligationVars contAppData,
            ProofObligationVars contAppData2,
            Services services) {
        ImmutableSet<BlockContract> ifContracts =
                services.getSpecificationRepository().getBlockContracts(blockContract.getBlock());
        ImmutableList<Term> contractsApplications =
                ImmutableSLList.<Term>nil();
        for (BlockContract cont : ifContracts) {
            InfFlowPOSnippetFactory f =
                    POSnippetFactory.getInfFlowFactory(cont, contAppData,
                                                       contAppData2, services);
            contractsApplications =
                    contractsApplications.append(
                    f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APPL));
        }
        return and(contractsApplications);
    }
}
