// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.mgt.ProofStatus;

public class CompoundProof extends ProofAggregate {

    private final ArrayList<ProofAggregate> proofs;
    
    CompoundProof(String name, ProofAggregate... proofs) {
        super(name);
        assert proofs!= null && proofs.length>=1;
        this.proofs = new ArrayList<>();
        Collections.addAll(this.proofs, proofs);
    }

    private void flatten(ProofAggregate p, List<Proof> l) {
       Collections.addAll(l, p.getProofs()); 
    }

    private void flatten(List<Proof> l) {
       for (ProofAggregate pa : proofs) {
          flatten(pa, l);
       }
   }
      
    @Override    
    public Proof[] getProofs() {
        List<Proof> l = new LinkedList<Proof>();
        flatten(l);
        return l.toArray(new Proof[l.size()]);
    }
        
    
    @Override
    public int size() {
        return proofs.size();
    }
    
        
    public ProofAggregate get(int i) {
        return proofs.get(i);
    }

    
    @Override    
    public List<ProofAggregate> getChildren() {
        return Collections.unmodifiableList(proofs);
    }
    
	@Override
	public ProofAggregate getChildrenAt(int i) {
		return proofs.get(i);
	}    
    
    @Override
    public ProofStatus getStatus() {
	ProofStatus result = proofs.get(0).getStatus();
	for(int i = 1; i < proofs.size(); i++) {
	    result = result.combine(proofs.get(i).getStatus());
	}
	return result;
    }


    @Override    
    public boolean equals(Object o) {
       if (!super.equals(o)) {
          return false;
       }
       
       final CompoundProof other = (CompoundProof) o;     
       
       for (int i = 0; i<proofs.size(); i++) {
          if (!proofs.get(i).equals(other.proofs.get(i))) { 
             return false;
          }
       }
       return true;
    }
 
   
    @Override    
    public int hashCode() {
        int result = 17;
        for (ProofAggregate proof : proofs){
            result = 37 * result + proof.hashCode();
        }
        return result;
    }
}