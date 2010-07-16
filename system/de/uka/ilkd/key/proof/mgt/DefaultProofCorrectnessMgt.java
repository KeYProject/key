// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;


import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.proofobligation.DefaultPOProvider;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.OperationContract;

public class DefaultProofCorrectnessMgt extends AbstractProofCorrectnessMgt {

    public DefaultProofCorrectnessMgt(Proof p) {
	super(p);
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    public void updateProofStatus() {
        //proof open?
        if(proof.openGoals().size() > 0) {
            proofStatus = ProofStatus.OPEN;
            return;
        }
	
        //which PO provider
        DefaultPOProvider poProvider = proof.getSettings().getProfile().getPOProvider();
        
        
        //used, but yet unproven specifications?
        for (RuleApp cachedRuleApp : cachedRuleApps) {
            RuleApp ruleApp = cachedRuleApp;
            RuleJustification ruleJusti = getJustification(ruleApp);
            if (ruleJusti instanceof RuleJustificationBySpec) {
                ContractWithInvs cwi
                        = ((RuleJustificationBySpec) ruleJusti).getSpec();
                for (OperationContract atomicContract
                        : proof.getServices().getSpecificationRepository()
                        .splitContract(cwi.contract)) {

                    InitConfig initConfig = proof.env().getInitConfig();
                    
                    ProofOblInput ensuresPostPO
                            = poProvider.createEnsuresPostPO(initConfig,
                            atomicContract,
                            cwi.assumedInvs);
                    ImmutableSet<Proof> ensuresPostProofs
                            = specRepos.getProofs(ensuresPostPO);
                    
                    ProofOblInput preservesInvPO
                            = poProvider.createPreservesInvPO(initConfig,
                            atomicContract.getProgramMethod(),
                            cwi.assumedInvs,
                            cwi.ensuredInvs);
                    ImmutableSet<Proof> preservesInvProofs
                            = specRepos.getProofs(preservesInvPO);
                    
                    ProofOblInput respectsModifiesPO
                            = poProvider.createRespectsModifiesPO(initConfig,
                            atomicContract,
                            cwi.assumedInvs);
                    ImmutableSet<Proof> respectsModifiesProofs
                            = specRepos.getProofs(respectsModifiesPO);

                    if (!(atLeastOneClosed(ensuresPostProofs)
                            && atLeastOneClosed(preservesInvProofs)
                            && atLeastOneClosed(respectsModifiesProofs))) {
                        proofStatus = ProofStatus.CLOSED_BUT_LEMMAS_LEFT;
                        return;
                    }
                }
            }
        }
        
        //no -> proof is closed
        proofStatus = ProofStatus.CLOSED;
    }

    

}
