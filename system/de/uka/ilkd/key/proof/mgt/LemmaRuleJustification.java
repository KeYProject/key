// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.RuleApp;

public abstract class LemmaRuleJustification implements RuleJustification{

    private RuleJustification getJustification(RuleApp r, ProofEnvironment env) {
	return env.getJustifInfo().getJustification(r, env.getInitialServices());
    }

    public DepAnalysis dependsOn(Proof p) {
        List list = getProofList();
        Iterator it = list.iterator();
        if (!it.hasNext()) {
            return DepAnalysis.getInstance(false, "No Proof available "
                    +"for method contract");
        }	
        while (it.hasNext()) {
            ProofAggregate pl=(ProofAggregate)it.next();
            if (pl==null) {
                return new DepAnalysis(false, "No proof in proof list "+
                "for method contract");
            }
            Proof[] proofs = pl.getProofs();
            for (int i=0; i<proofs.length; i++) {	   
                Proof curr = proofs[i];
                if (curr==p) {
                    return DepAnalysis.getInstance(true, null, curr, 
                            "Direct dependency from "
                            +"rule to proof.");
                }
            }
        }
        it = list.iterator();
        while (it.hasNext()) {
            ProofAggregate pl=(ProofAggregate)it.next();
            Proof[] proofs = pl.getProofs();
            for (int i=0; i<proofs.length; i++) {	   
                Proof curr = proofs[i];
                Iterator nonAxIt = curr.mgt().getAppliedNonAxioms();
                while (nonAxIt.hasNext()) {
                    RuleApp nonAx = (RuleApp) nonAxIt.next();
                    DepAnalysis ana = getJustification(nonAx, 
                            p.env()).dependsOn(p);
                    if (ana.depExists()) {
                        return DepAnalysis.getInstance(true, null, curr, 
                                "Indirect dependency from "
                                +"rule to proof.");
                    }
                }
            }
        }
        return DepAnalysis.getInstance(false, null, null);	
    }
    
    public boolean isAxiomJustification() {
	return false;
    }
    


}
