// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.util.Debug;

public class CompoundProof extends ProofAggregate {

    private final ProofAggregate[] proofs;
    
    CompoundProof(ProofAggregate[] proofs, String name) {
        super(name);
        if (proofs.length<=1) Debug.fail();
        this.proofs=proofs;
    }

    private void addProofsToList(List<Proof> l) {
        for (int i=0; i<size(); i++) {
            if (proofs[i] instanceof SingleProof) {
                l.add(proofs[i].getFirstProof());
            } else {
                ((CompoundProof)proofs[i]).addProofsToList(l);
            }
        }
    }
    
    @Override    
    public Proof[] getProofs() {
        List<Proof> l = new LinkedList<Proof>();
        addProofsToList(l);
        return l.toArray(new Proof[l.size()]);
    }
        
    
    @Override
    public int size() {
        return proofs.length;
    }
    
        
    public ProofAggregate get(int i) {
        return proofs[i];
    }

    
    @Override    
    public ProofAggregate[] getChildren() {
        return proofs;
    }
    
    
    @Override
    public ProofStatus getStatus() {
	ProofStatus result = proofs[0].getStatus();
	for(int i = 1; i < proofs.length; i++) {
	    result = result.combine(proofs[i].getStatus());
	}
	return result;
    }


    @Override    
    public boolean equals(Object o) {
        if (!(o instanceof CompoundProof)) return false;
        CompoundProof cmp = (CompoundProof) o;
        for (int i=0; i<cmp.size(); i++) {
            if (!cmp.get(i).equals(get(i))) return false;
        }
        return true;
    }
 
   
    @Override    
    public int hashCode() {
        int result = 17;
        for (int i=0; i < size(); i++){
            result = 37 * result + get(i).hashCode();
        }
        return result;
    }    
}
