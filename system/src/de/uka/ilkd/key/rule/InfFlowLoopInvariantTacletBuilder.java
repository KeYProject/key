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

import de.uka.ilkd.key.java.Services;
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
        extends AbstractInfFlowContractTacletBuilder {
    
    private LoopInvariant loopinvariant;
    
    public void setInvariant(LoopInvariant invariant) {
        this.loopinvariant = invariant;
    }
    
    public InfFlowLoopInvariantTacletBuilder(final Services services) {
        super(services);
    }

    @Override
    Name generateName() {
        return MiscTools.toValidTacletName("Use information flow contract for " +
                                           loopinvariant.getName().toString());
    }

    @Override
    Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                               Services services) {
        BasicPOSnippetFactory fAssumes =
                POSnippetFactory.getBasicFactory(loopinvariant, schemaDataAssumes, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
        // TODO: Think about correctness
    }

    @Override
    Term generateSchemaFind(ProofObligationVars schemaDataFind,
                            Services services) {
        BasicPOSnippetFactory fFind =
                POSnippetFactory.getBasicFactory(loopinvariant, schemaDataFind, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
        // TODO: Think about correctness
    }

    @Override
    Term getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
                POSnippetFactory.getBasicFactory(loopinvariant, appData,
                                                 services);
        return f.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
        // TODO: Think about correctness
    }

    @Override
    Term buildContractApplications(ProofObligationVars contAppData,
                                   ProofObligationVars contAppData2,
                                   Services services) {
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(loopinvariant, contAppData,
                        contAppData2, services);
        return f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APPL);
        // TODO: Think about correctness
    }
}