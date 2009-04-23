// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofStatus;

public abstract class ProofAggregate {

    private String name;
    protected ProofStatus proofStatus = null;

    protected ProofAggregate(String name) {
        this.name=name;
    }
    
    public static ProofAggregate createProofAggregate(ProofAggregate[] proofs, String name) {
        if (proofs.length>1) {            
            return new CompoundProof(proofs, name);
        } else {
            return proofs[0];
        }
    }
    
    public static ProofAggregate createProofAggregate(Proof[] proofs, String name) {
        if (proofs.length==0) return null; // needed for tests
        if (proofs.length>1) {
            SingleProof singles[] = new SingleProof[proofs.length];
            for (int i=0; i<proofs.length; i++) {
                singles[i] = new SingleProof(proofs[i], name);
            }
            return new CompoundProof(singles, name);
        } else {
            return new SingleProof(proofs[0], name);
        }
    }
    
    public static ProofAggregate createProofAggregate(Proof proof, String name) {
        return new SingleProof(proof, name);
    }
    
    public abstract Proof[] getProofs();
    
    public Proof getFirstProof() {
        return getProofs()[0];
    }

    public void setProofEnv(ProofEnvironment env) {
        Proof[] proofs = getProofs();
        for (int i=0; i<proofs.length; i++) {
            proofs[i].setProofEnv(env);
        }
    }

    public abstract int size();

    public String description() {
        return name;
    }

    public String toString() {	
        return name;
    }

    public abstract void updateProofStatus();
    
    
    public ProofStatus getStatus() {
        if (proofStatus==null) updateProofStatus();
        return proofStatus;	
    }
    
    public abstract ProofAggregate[] getChildren();
 
    
}
