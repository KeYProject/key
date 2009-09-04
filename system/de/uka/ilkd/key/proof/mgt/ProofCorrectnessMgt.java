// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.Contract;

public interface ProofCorrectnessMgt {

    /**
     * Tells whether a contract for the passed target may be applied 
     * in the passed goal without creating circular dependencies.
     */    
    boolean contractApplicableFor(KeYJavaType kjt, 
	                          ObserverFunction target, 
	                          Goal g);

    ProofStatus getStatus();

    void updateProofStatus();
    
    void ruleApplied(RuleApp r);

    void ruleUnApplied(RuleApp r);
        
    ImmutableSet<Contract> getUsedContracts();

    void setMediator(KeYMediator mediator);

    boolean proofSimilarTo(Proof p);

    RuleJustification getJustification(RuleApp app);
    
    void removeProofListener();
}
