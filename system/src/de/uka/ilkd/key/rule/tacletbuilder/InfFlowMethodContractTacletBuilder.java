// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.rule.tacletbuilder.AbstractInfFlowContractAppTacletBuilder;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public final class InfFlowMethodContractTacletBuilder
        extends AbstractInfFlowContractAppTacletBuilder {

    private FunctionalOperationContract methodContract;


    public InfFlowMethodContractTacletBuilder(final Services services) {
        super(services);
    }


    public void setContract(FunctionalOperationContract contract) {
        this.methodContract = contract;
    }


    @Override
    Name generateName() {
        return MiscTools.toValidTacletName(USE_IF + methodContract.getTarget().getUniqueName());
    }


    @Override
    Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                               Services services) {
        BasicPOSnippetFactory fAssumes =
                POSnippetFactory.getBasicFactory(methodContract, schemaDataAssumes, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    Term generateSchemaFind(ProofObligationVars schemaDataFind,
                            Services services) {
        BasicPOSnippetFactory fFind =
                POSnippetFactory.getBasicFactory(methodContract, schemaDataFind, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    Term getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
                POSnippetFactory.getBasicFactory(methodContract, appData,
                                                 services);
        return f.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    Term buildContractApplications(ProofObligationVars contAppData,
                                   ProofObligationVars contAppData2,
                                   Services services) {
        ImmutableSet<InformationFlowContract> ifContracts =
                getInformFlowContracts(methodContract.getTarget(), services);
        ImmutableList<Term> contractsApplications =
                ImmutableSLList.<Term>nil();
        for (InformationFlowContract cont : ifContracts) {
            InfFlowPOSnippetFactory f =
                    POSnippetFactory.getInfFlowFactory(cont, contAppData,
                                                       contAppData2, services);
            contractsApplications =
                    contractsApplications.append(
                    f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APPL));
        }

        return and(contractsApplications);
    }


    private ImmutableSet<InformationFlowContract> getInformFlowContracts(IProgramMethod pm,
                                                                         Services services) {
        ImmutableSet<Contract> contracts =
                services.getSpecificationRepository().getContracts(pm.getContainerType(), pm);
        ImmutableSet<InformationFlowContract> ifContracts =
                DefaultImmutableSet.<InformationFlowContract>nil();
        for (Contract c : contracts) {
            if (c instanceof InformationFlowContract) {
                ifContracts = ifContracts.add((InformationFlowContract) c);
            }
        }
        return ifContracts;
    }
}