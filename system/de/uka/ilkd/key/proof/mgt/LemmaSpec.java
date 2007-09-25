// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;

public class LemmaSpec extends AbstractContract {
    
    private NoPosTacletApp lemma;

    public LemmaSpec(NoPosTacletApp lemma) {
	this.lemma = lemma;
    }

    public Taclet getLemmaAndRegister() {
	return lemma.taclet();
    }

    public Object getObjectOfContract() {
	return lemma;
    }

    public ProofOblInput getProofOblInput(Proof proof) {
	return null; // not implemented yet
    }

    public String toString() {
	return "Lemma specification: "+lemma;
    }

    public boolean equals(Object cmp) {
	if (!(cmp instanceof LemmaSpec)) return false;	
	return lemma.equals(((LemmaSpec)cmp).lemma);
    }

    public int hashCode() {
	return lemma.hashCode();
    }
    
    public String getName() {
        return toString();
    }
    

}
