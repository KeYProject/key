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

import java.util.*;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
import de.uka.ilkd.key.jml.JMLClassSpec;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;
import de.uka.ilkd.key.speclang.SLListOfClassInvariant;
import de.uka.ilkd.key.speclang.TranslatedClassInvariant;

/** 
 * The repository where all specification (contracts) of a proof
 * environment are contained. An instance must belong to only one
 * {@link ProofEnvironment}.
 */
public class SpecificationRepository {
    
    private Map contracts = new HashMap();
    private LinkedHashMap invariants = null;
    private Services services;
     
    public SpecificationRepository(Services services) {
        this.services = services;
    }
    
    // TODO: ensure fixed order (?)
    private void createClassInvariants() {   
        final SortedSet allClassesSorted = 
            new TreeSet(new KeYJavaType.LexicographicalKeYJavaTypeOrder());
        allClassesSorted.addAll(services.getJavaInfo().getAllKeYJavaTypes());
        
        final Iterator it = allClassesSorted.iterator();
        invariants = new LinkedHashMap();
        while (it.hasNext()) {
            final KeYJavaType kjt    = (KeYJavaType) it.next();
            final JMLClassSpec jmlcs = services.getImplementation2SpecMap().getSpecForClass(kjt);
            if (jmlcs!=null) {
                SetOfTerm terms = jmlcs.getAllQuantifiedInvariants();
                IteratorOfTerm it2 = terms.iterator();
                while (it2.hasNext()) {
                    Term t = it2.next();
                    if (t!=null) {
                        ClassInvariant inv = new TranslatedClassInvariant(
                                new JavaModelClass(kjt, 
                                        services.getJavaInfo().getJavaSourcePath(), 
                                        services), t, services);
                        ListOfClassInvariant invs = (ListOfClassInvariant) invariants.get(kjt);
                        if (invs==null) {
                            invs = SLListOfClassInvariant.EMPTY_LIST;
                        }
                        invariants.put(kjt, invs.prepend(inv));
                    }
                }
            }
        }                  
    }
    
    /** returns an iterator of specifications ({@link Contract})
     * contained in this repository. Modifications to the underlying
     * set are not allowed.
     */
    public Iterator getSpecs() {
	return contracts.values().iterator();
    }

    public Contract getContractByName(String name) {
        Iterator it = contracts.entrySet().iterator();
        while (it.hasNext()) {
            Contract ct = (Contract)((ContractSet) 
                     ((Map.Entry)it.next()).getValue()).iterator().next();
            if (ct.getName().equals(name)) {
                return ct;
            }
        }
        return null;
    }
    
    /** returns a set of contracts with the argument as identifying
     * contracted object.
     */
    public ContractSet getContract(Object objOfContract) {
    	Object o = objOfContract;
    	if(objOfContract instanceof ModelMethod) {
    		o = convertToProgramMethod((ModelMethod)objOfContract);
    	}
	    return (ContractSet) contracts.get(o);
    }
    
    /** returns a set of contracts with one of the elements in 
     * the argument list as identifying contracted object.
     */
    public ContractSet getContracts(ListOfProgramMethod objsOfContract,
                                    Modality modality) {
        ContractSet ctSet = new ContractSet();
        IteratorOfProgramMethod it = objsOfContract.iterator();
        while (it.hasNext()) {
            ContractSet cs = getContract(it.next());
            if (cs!=null) {
                ctSet.addAll(cs.getMethodContracts(modality));
            }
        }
        return ctSet;
    }
    
    /** returns a set of contracts with the argument as identifying
     * contracted object.
     */
    public ContractSet getContract(Object objOfContract, Modality modality) {
        ContractSet ctSet = getContract(objOfContract);
        if (ctSet==null) {
            return new ContractSet();            
        }
        ctSet = ctSet.getMethodContracts(modality);
        if (ctSet==null) {
            return new ContractSet();
        }
        return ctSet;
    }
        
    
    /** adds a contract to this specification repository.
     */
    public Contract add(Contract ct) {
	Object o = ct.getObjectOfContract();
	if (o instanceof ModelMethod) {
		o = convertToProgramMethod((ModelMethod)o);
	}
	ContractSet cs =(ContractSet) contracts.get(o);
	if (cs==null) {
	    cs = new ContractSet();
	    contracts.put(o, cs);
	}	
	return cs.add(ct);
    }
    
    public void removeProofList(ProofAggregate pl) {
	Iterator it = getSpecs();
	while (it.hasNext()) {
	    Object o = it.next();
	    ((ContractSet) o).removeProofList(pl);
	}
    }
    
    public ListOfClassInvariant getAllInvariantsForType(KeYJavaType kjt) {
        if (invariants == null) {
            createClassInvariants();
        }
        return invariants.containsKey(kjt) ? (ListOfClassInvariant) invariants.get(kjt)
                : SLListOfClassInvariant.EMPTY_LIST;
    }
        
    public SpecificationRepository copy(Services s) {
        final SpecificationRepository res = new SpecificationRepository(s);
        res.contracts  = this.contracts; //TODO deepcopy
        res.invariants = this.invariants; //TODO
        return res;
    }

//------------------------ Helper methods -----------------------------//
    
    private ProgramMethod convertToProgramMethod(ModelMethod m) {
    	JavaInfo javaInfo = services.getJavaInfo();
    	KeYJavaType containingClass = javaInfo.getKeYJavaTypeByClassName(m.getContainingClassName());
    	String name = m.getName();
    	
    	ListOfKeYJavaType signature = SLListOfKeYJavaType.EMPTY_LIST;    	
    	for(int i=0;i<m.getNumParameters();i++) {
    		signature = signature.append(javaInfo.getKeYJavaType(m.getParameterTypeAt(i)));
    	}
    	
    	return javaInfo.getProgramMethod(containingClass,name,signature,javaInfo.getJavaLangObject());
    }
    
}

