/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;


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
    Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes, Services services) {
        BasicPOSnippetFactory fAssumes =
            POSnippetFactory.getBasicFactory(methodContract, schemaDataAssumes, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    Term generateSchemaFind(ProofObligationVars schemaDataFind, Services services) {
        BasicPOSnippetFactory fFind =
            POSnippetFactory.getBasicFactory(methodContract, schemaDataFind, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    Term getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
            POSnippetFactory.getBasicFactory(methodContract, appData, services);
        return f.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    Term buildContractApplications(ProofObligationVars contAppData,
            ProofObligationVars contAppData2, Services services) {
        ImmutableSet<InformationFlowContract> ifContracts =
            getInformFlowContracts(methodContract.getTarget(), services);
        ImmutableList<Term> contractsApplications = ImmutableSLList.nil();
        for (InformationFlowContract cont : ifContracts) {
            InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(cont, contAppData, contAppData2, services);
            contractsApplications = contractsApplications
                    .append(f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APPL));
        }

        return and(contractsApplications);
    }


    private ImmutableSet<InformationFlowContract> getInformFlowContracts(IProgramMethod pm,
            Services services) {
        ImmutableSet<Contract> contracts =
            services.getSpecificationRepository().getContracts(pm.getContainerType(), pm);
        ImmutableSet<InformationFlowContract> ifContracts =
            DefaultImmutableSet.nil();
        for (Contract c : contracts) {
            if (c instanceof InformationFlowContract) {
                ifContracts = ifContracts.add((InformationFlowContract) c);
            }
        }
        return ifContracts;
    }
}
