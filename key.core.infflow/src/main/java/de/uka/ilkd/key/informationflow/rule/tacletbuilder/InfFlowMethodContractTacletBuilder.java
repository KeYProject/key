/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.infflow.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
@NullMarked
public final class InfFlowMethodContractTacletBuilder
        extends AbstractInfFlowContractAppTacletBuilder {

    private @Nullable FunctionalOperationContract methodContract;


    public InfFlowMethodContractTacletBuilder(final Services services) {
        super(services);
    }


    public void setContract(FunctionalOperationContract contract) {
        this.methodContract = contract;
    }


    @Override
    Name generateName() {
        return MiscTools.toValidTacletName(USE_IF + requireMethodContract().getTarget()
                .getUniqueName());
    }


    @Override
    JTerm generateSchemaAssumes(ProofObligationVars schemaDataAssumes, Services services) {
        BasicPOSnippetFactory fAssumes =
            POSnippetFactory.getBasicFactory(requireMethodContract(), schemaDataAssumes, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    JTerm generateSchemaFind(ProofObligationVars schemaDataFind, Services services) {
        BasicPOSnippetFactory fFind =
            POSnippetFactory.getBasicFactory(requireMethodContract(), schemaDataFind, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    JTerm getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
            POSnippetFactory.getBasicFactory(requireMethodContract(), appData, services);
        return f.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION);
    }


    @Override
    JTerm buildContractApplications(ProofObligationVars contAppData,
            ProofObligationVars contAppData2, Services services) {
        ImmutableSet<InformationFlowContract> ifContracts =
            getInformFlowContracts(requireMethodContract().getTarget(), services);
        ImmutableList<JTerm> contractsApplications = ImmutableList.nil();
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
        final KeYJavaType containerType = pm.getContainerType();
        if (containerType == null) {
            throw new NullPointerException(
                "No container type for the method " + pm.getUniqueName() + ".");
        }
        ImmutableSet<Contract> contracts =
            services.getSpecificationRepository().getContracts(containerType, pm);
        ImmutableSet<InformationFlowContract> ifContracts =
            DefaultImmutableSet.nil();
        for (Contract c : contracts) {
            if (c instanceof InformationFlowContract) {
                ifContracts = ifContracts.add((InformationFlowContract) c);
            }
        }
        return ifContracts;
    }


    private FunctionalOperationContract requireMethodContract() {
        final FunctionalOperationContract c = methodContract;
        if (c == null) {
            throw new NullPointerException(
                "No method contract for building the information flow method contract taclet.");
        }
        return c;
    }
}
