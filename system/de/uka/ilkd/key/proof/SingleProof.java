// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof;

public class SingleProof extends ProofAggregate {

    private Proof proof;
    
    public SingleProof(Proof p, String name) {
        super(name);
        this.proof = p;
    }
    
    public void updateProofStatus() {
        proof.mgt().updateProofStatus();
        proofStatus = proof.mgt().getStatus();
    }

    public Proof[] getProofs() {
        return new Proof[]{proof};
    }
    
    public int size() {
        return 1;
    }
    
    public ProofAggregate[] getChildren() {
        return new ProofAggregate[0];
    }
}
