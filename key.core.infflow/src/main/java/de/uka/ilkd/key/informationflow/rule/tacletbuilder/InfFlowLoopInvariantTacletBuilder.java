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
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Implements the rule which inserts loop invariants for a method call.
 */
@NullMarked
public final class InfFlowLoopInvariantTacletBuilder
        extends AbstractInfFlowContractAppTacletBuilder {

    private @Nullable LoopSpecification loopinvariant;
    private @Nullable ExecutionContext executionContext;
    private @Nullable JTerm guard;

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
        return MiscTools.toValidTacletName(USE_IF + requireLoopInvariant().getUniqueName());
    }

    @Override
    JTerm generateSchemaAssumes(ProofObligationVars schemaDataAssumes, Services services) {
        BasicPOSnippetFactory fAssumes = POSnippetFactory.getBasicFactory(requireLoopInvariant(),
            schemaDataAssumes, requireExecutionContext(), requireGuard(), services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }

    @Override
    JTerm generateSchemaFind(ProofObligationVars schemaDataFind, Services services) {
        BasicPOSnippetFactory fFind = POSnippetFactory.getBasicFactory(requireLoopInvariant(),
            schemaDataFind, requireExecutionContext(), requireGuard(), services);
        return fFind.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }

    @Override
    JTerm getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f = POSnippetFactory.getBasicFactory(requireLoopInvariant(),
            appData, requireExecutionContext(), requireGuard(), services);
        return f.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }


    @Override
    JTerm buildContractApplications(ProofObligationVars contAppData,
            ProofObligationVars contAppData2, Services services) {
        LoopSpecification ifContract =
            services.getSpecificationRepository().getLoopSpec(requireLoopInvariant().getLoop());
        if (ifContract == null) {
            throw new NullPointerException(
                "No matching loop specification for the loop invariant "
                    + requireLoopInvariant().getUniqueName() + ".");
        }

        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(ifContract, contAppData,
            contAppData2, requireExecutionContext(), requireGuard(), services);
        JTerm contractApplication =
            f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_LOOP_INVARIANT_APPL);

        return contractApplication;
    }


    private LoopSpecification requireLoopInvariant() {
        final LoopSpecification loop = loopinvariant;
        if (loop == null) {
            throw new NullPointerException(
                "No loop invariant for building the information flow loop invariant taclet.");
        }
        return loop;
    }


    private ExecutionContext requireExecutionContext() {
        final ExecutionContext context = executionContext;
        if (context == null) {
            throw new NullPointerException(
                "No execution context for building the information flow loop invariant taclet.");
        }
        return context;
    }


    private JTerm requireGuard() {
        final JTerm g = guard;
        if (g == null) {
            throw new NullPointerException(
                "No guard for building the information flow loop invariant taclet.");
        }
        return g;
    }
}
