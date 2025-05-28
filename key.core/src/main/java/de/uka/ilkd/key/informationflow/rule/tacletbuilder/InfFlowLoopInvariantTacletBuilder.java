/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;


/**
 * Implements the rule which inserts loop invariants for a method call.
 */
public final class InfFlowLoopInvariantTacletBuilder
        extends AbstractInfFlowContractAppTacletBuilder {

    private LoopSpecification loopinvariant;
    private ExecutionContext executionContext;
    private JTerm guard;

    public InfFlowLoopInvariantTacletBuilder(final Services services) {
        super(services);
    }

    public void setInvariant(LoopSpecification invariant) {
        this.loopinvariant = invariant;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    public void setGuard(JTerm guard) {
        this.guard = guard;
    }


    @Override
    Name generateName() {
        return MiscTools.toValidTacletName(USE_IF + loopinvariant.getUniqueName());
    }

    @Override
    JTerm generateSchemaAssumes(ProofObligationVars schemaDataAssumes, Services services) {
        BasicPOSnippetFactory fAssumes = POSnippetFactory.getBasicFactory(loopinvariant,
            schemaDataAssumes, executionContext, guard, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }

    @Override
    JTerm generateSchemaFind(ProofObligationVars schemaDataFind, Services services) {
        BasicPOSnippetFactory fFind = POSnippetFactory.getBasicFactory(loopinvariant,
            schemaDataFind, executionContext, guard, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }

    @Override
    JTerm getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f = POSnippetFactory.getBasicFactory(loopinvariant, appData,
            executionContext, guard, services);
        return f.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }


    @Override
    JTerm buildContractApplications(ProofObligationVars contAppData,
            ProofObligationVars contAppData2, Services services) {
        LoopSpecification ifContract =
            services.getSpecificationRepository().getLoopSpec(loopinvariant.getLoop());

        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(ifContract, contAppData,
            contAppData2, executionContext, guard, services);
        JTerm contractApplication =
            f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_LOOP_INVARIANT_APPL);

        return contractApplication;
    }
}
