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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Implements the rule which inserts loop invariants for a method call.
 */
public final class InfFlowLoopInvariantTacletBuilder
        extends AbstractInfFlowContractAppTacletBuilder {
    
    private LoopInvariant loopinvariant;    
    private ExecutionContext executionContext;
    private Term guard;

    public InfFlowLoopInvariantTacletBuilder(final Services services) {
        super(services);
    }
    
    public void setInvariant(LoopInvariant invariant) {
        this.loopinvariant = invariant;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    public void setGuard(Term guard) {
        this.guard = guard;
    }


    @Override
    Name generateName() {
        return MiscTools.toValidTacletName(USE_IF + loopinvariant.getUniqueName());
    }

    @Override
    Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                               Services services) {        
        BasicPOSnippetFactory fAssumes =
                POSnippetFactory.getBasicFactory(loopinvariant,
                                                 schemaDataAssumes,
                                                 executionContext,
                                                 guard,
                                                 services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }

    @Override
    Term generateSchemaFind(ProofObligationVars schemaDataFind,
                            Services services) {
        BasicPOSnippetFactory fFind =
                POSnippetFactory.getBasicFactory(loopinvariant,
                                                 schemaDataFind,
                                                 executionContext,
                                                 guard,
                                                 services);
        return fFind.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }

    @Override
    Term getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
                POSnippetFactory.getBasicFactory(loopinvariant,
                                                 appData,
                                                 executionContext,
                                                 guard,
                                                 services);
        return f.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
    }


    @Override
    Term buildContractApplications(ProofObligationVars contAppData,
                                   ProofObligationVars contAppData2,
                                   Services services) {
        LoopInvariant ifContract =
                services.getSpecificationRepository().getLoopInvariant(loopinvariant.getLoop());

        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(ifContract, contAppData,
                                                   contAppData2,
                                                   executionContext,
                                                   guard, services);
        Term contractApplication =
                f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_LOOP_INVARIANT_APPL);

        return contractApplication;
    }
}