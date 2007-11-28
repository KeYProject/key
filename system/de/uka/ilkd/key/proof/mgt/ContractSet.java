// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;


import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.ProofAggregate;

/** represents a set of contracts (@link{Contract}}) with attached proofs.*/
public class ContractSet {
    
    private List contracts = new LinkedList();

    public Contract add(Contract ct) {
        Iterator it = contracts.iterator();
        while (it.hasNext()) {
            Contract c = (Contract) it.next();
            if (c.equals(ct)) {
                return c;
            }
        }
        contracts.add(ct);
        return ct;
    }
    
    public void addAll(ContractSet cs) {
        if (cs==null) return;
        Iterator it = cs.iterator();
        while (it.hasNext()) {
            add((Contract)it.next());
        }
    }

    public Iterator iterator() {
	return contracts.iterator();
    }

    public void removeProofList(ProofAggregate pl) {
	for (final Iterator it=iterator(); it.hasNext();) {
            ((Contract)it.next()).removeCompoundProof(pl);       
        }
    }
    
    public int size() {
        return contracts.size();
    }
    
    public Contract[] toArray() {
        return (Contract[]) contracts.toArray(new Contract[contracts.size()]);
    }
    
    /** returns a set of contracts with the argument as identifying
     * contracted object and the matching modality
     */
    public ContractSet getMethodContracts(Modality modality) {
        ContractSet result = new ContractSet();
        Iterator it = iterator();
        while (it.hasNext()) {
            Contract ct = (Contract) it.next(); 
            if (ct instanceof OldOperationContract 
                    && ((OldOperationContract)ct).applicableForModality(modality)) {
                result.add(ct);
            }
        }
        return result;
    }
    

}
