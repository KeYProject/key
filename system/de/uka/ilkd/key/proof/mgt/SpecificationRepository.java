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

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.*;


public final class SpecificationRepository {
    
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final Map<ProgramMethod, ImmutableSet<OperationContract>> contracts 
    		= new LinkedHashMap<ProgramMethod,ImmutableSet<OperationContract>>();
    private final Map<String,OperationContract> contractsByName
                = new LinkedHashMap<String,OperationContract>();
    private final Map<Operator,DependencyContract> depContracts
    		= new LinkedHashMap<Operator,DependencyContract>();
    private final Map<KeYJavaType,ImmutableSet<ClassInvariant>> invs
    		= new LinkedHashMap<KeYJavaType, ImmutableSet<ClassInvariant>>();
    private final Map<KeYJavaType,ImmutableSet<ClassAxiom>> axioms
    		= new LinkedHashMap<KeYJavaType, ImmutableSet<ClassAxiom>>();
    private final Map<ProofOblInput,ImmutableSet<Proof>> proofs
                = new LinkedHashMap<ProofOblInput,ImmutableSet<Proof>>();
    private final Map<LoopStatement,LoopInvariant> loopInvs
                = new LinkedHashMap<LoopStatement,LoopInvariant>();
    private final Services services;
    
    private int contractCounter = 0;
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 

    public SpecificationRepository(Services services) {
	this.services = services;
    }
    

    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    /**
     * Returns all known class invariants for the passed type.
     */
    private ImmutableSet<ClassInvariant> getClassInvariants(KeYJavaType kjt) {
	ImmutableSet<ClassInvariant> result = invs.get(kjt);
	return result == null 
	       ? DefaultImmutableSet.<ClassInvariant>nil() 
               : result;
    }    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    /**
     * Returns all registered (atomic) contracts for the passed operation.
     */
    public ImmutableSet<OperationContract> getOperationContracts(
	    					ProgramMethod pm) {
	ImmutableSet<OperationContract> result = contracts.get(pm);
        return result == null 
               ? DefaultImmutableSet.<OperationContract>nil() 
               : result;
    }
    
    
    /**
     * Returns all registered (atomic) contracts for the passed operation which 
     * refer to the passed modality.
     */
    public ImmutableSet<OperationContract> getOperationContracts(
	    					ProgramMethod pm, 
	    					Modality modality) {
	ImmutableSet<OperationContract> result = getOperationContracts(pm);
	for(OperationContract contract : result) {
	    if(!contract.getModality().equals(modality)) {
		result = result.remove(contract);
	    }
	}
	return result;
    }
    

    /**
     * Returns the registered (atomic or combined) contract corresponding to the 
     * passed name, or null.
     */
    public OperationContract getOperationContractByName(String name) {
        if(name == null || name.length() == 0) {
            return null;
        }
        
        String[] baseNames = name.split(CONTRACT_COMBINATION_MARKER);        
        ImmutableSet<OperationContract> baseContracts 
            = DefaultImmutableSet.<OperationContract>nil();
        for(String baseName : baseNames) {
            OperationContract baseContract = contractsByName.get(baseName);
            if(baseContract == null) {
                return null;
            }
            baseContracts = baseContracts.add(baseContract);
        }
        
        return combineContracts(baseContracts);
    }
    
    
    /**
     * Returns a set encompassing the passed contract and all its versions 
     * inherited to overriding methods.
     */
    public ImmutableSet<OperationContract> getInheritedContracts(
	    					OperationContract contract) {
	ImmutableSet<OperationContract> result 
		= DefaultImmutableSet.<OperationContract>nil().add(contract);
        final ImmutableSet<ProgramMethod> pms 
        	= services.getJavaInfo()
        	          .getOverridingMethods(contract.getProgramMethod());
        for(ProgramMethod pm : pms) {
            for(OperationContract pmContract : getOperationContracts(pm)) {
        	if(pmContract.id() == contract.id()) {
        	    result = result.add(pmContract);
        	    break;
        	}
            }
        }
        return result;
    }
    
    
    /**
     * Returns a set encompassing the passed contracts and all its versions 
     * inherited to overriding methods.
     */    
    public ImmutableSet<OperationContract> getInheritedContracts(
	    			ImmutableSet<OperationContract> contractSet) {
	ImmutableSet<OperationContract> result 
		= DefaultImmutableSet.<OperationContract>nil();
        for(OperationContract c : contractSet) {
            result = result.union(getInheritedContracts(c));
        }
        return result;
    }
        
    
    /**
     * Registers the passed (atomic) operation contract, and inherits it to all
     * overriding methods.
     */
    public void addOperationContract(OperationContract contract) {
	//set id
	contract = contract.setID(contractCounter++);

	//register and inherit
        final ImmutableSet<ProgramMethod> pms 
        	= services.getJavaInfo()
        	          .getOverridingMethods(contract.getProgramMethod())
        	          .add(contract.getProgramMethod());
        for(ProgramMethod pm : pms) {
            contract = contract.setProgramMethod(pm, services);
            assert contractsByName.get(contract.getName()) == null
                   : "Tried to add a contract with a non-unique name!";
            assert !contract.getName().contains(CONTRACT_COMBINATION_MARKER)
                   : "Tried to add a contract with a name containing the"
                     + " reserved character " 
                     + CONTRACT_COMBINATION_MARKER 
                     + "!";
            assert contract.id() != OperationContract.INVALID_ID
                   : "Tried to add a contract with an invalid id!";
            contracts.put(pm, getOperationContracts(pm).add(contract));
            contractsByName.put(contract.getName(), contract);
        }
    }
    
    
    /**
     * Registers the passed contracts.
     */
    public void addOperationContracts(ImmutableSet<OperationContract> toAdd) {
        for(OperationContract contract : toAdd) {
            addOperationContract(contract);
        }
    }
    
    
    /**
     * Creates a combined contract out of the passed atomic contracts.
     */
    public OperationContract combineContracts(
                                    ImmutableSet<OperationContract> toCombine) {
        assert toCombine != null && toCombine.size() > 0;
        for(OperationContract contract : toCombine) {            
            assert !contract.getName().contains(CONTRACT_COMBINATION_MARKER)
                   : "Please combine only atomic contracts!";
        }

        //sort contracts alphabetically (for determinism)
        OperationContract[] contractsArray 
        	= toCombine.toArray(new OperationContract[toCombine.size()]);
        Arrays.sort(contractsArray, new Comparator<OperationContract> () {
            public int compare(OperationContract c1, OperationContract c2) {
                return c1.getName().compareTo(c2.getName());
            }
        });
        
        //split
        OperationContract contract = contractsArray[0];
        OperationContract[] others 
            = new OperationContract[contractsArray.length - 1];
        System.arraycopy(contractsArray, 
                         1, 
                         others, 
                         0, 
                         contractsArray.length - 1);
        
        //determine names
        StringBuffer nameSB = new StringBuffer(contract.getName());
        for(OperationContract other : others) {
            nameSB.append(CONTRACT_COMBINATION_MARKER + other.getName());
        }
        
        return contract.union(
                others, 
                nameSB.toString(), 
                services);
    }
    
    
    /**
     * Splits the passed contract into its atomic components. 
     */
    public ImmutableSet<OperationContract> splitContract(
	    					OperationContract contract) {
        ImmutableSet<OperationContract> result 
        	= DefaultImmutableSet.<OperationContract>nil();
        String[] atomicNames 
            = contract.getName().split(CONTRACT_COMBINATION_MARKER);
        for(String atomicName : atomicNames) {
            OperationContract atomicContract = contractsByName.get(atomicName);
            if(atomicContract == null) {
                return null;
            }
            assert atomicContract.getProgramMethod()
                                 .equals(contract.getProgramMethod());
            result = result.add(atomicContract);
        }
        return result;
    }
    
    
    public DependencyContract getDependencyContract(Operator obs) {
	return depContracts.get(obs);
    }
    
    
    public void addDependencyContract(DependencyContract depContract) {
	depContracts.put(depContract.getObserver(), depContract);
    }
    
        
    /**
     * Registers the passed class invariant, whose name must be different from 
     * all previously registered class invariants.
     */
    public void addClassInvariant(ClassInvariant inv) {
        KeYJavaType kjt = inv.getKJT();
        invs.put(kjt, getClassInvariants(kjt).add(inv));
    }
    
    
    /**
     * Registers the passed class invariants.
     */
    public void addClassInvariants(ImmutableSet<ClassInvariant> toAdd) {
        for(ClassInvariant inv : toAdd) {
            addClassInvariant(inv);
        }
    }
    
    /**
     * Returns all class axioms registered for the passed class, including
     * the one defined by the class invariants registered for the class.
     */
    public ImmutableSet<ClassAxiom> getClassAxioms(KeYJavaType kjt) {
	//get registered axioms
	ImmutableSet<ClassAxiom> result = axioms.get(kjt);
	if(result == null) {
	    result = DefaultImmutableSet.<ClassAxiom>nil();
	}
	
	//add invariant axiom
	ImmutableSet<ClassInvariant> myInvs = getClassInvariants(kjt);
	ProgramVariable selfVar = TB.selfVar(services, kjt, false);
	Term invDef = TB.tt();
	for(ClassInvariant inv : myInvs) {
	    invDef = TB.and(invDef, inv.getInv(selfVar, services));
	}
	invDef = TB.equals(TB.inv(services, TB.var(selfVar)), invDef);
	ClassAxiom invAxiom = new ClassAxiomImpl("Class invariant axiom",
		                                 kjt,
		                                 invDef,
		                                 selfVar);
	result = result.add(invAxiom);
	
	return result;
    }
    
    
    /**
     * Registers the passed class axiom.
     */
    public void addClassAxiom(ClassAxiom ax) {
        KeYJavaType kjt = ax.getKJT();
        ImmutableSet<ClassAxiom> currentAxioms = axioms.get(kjt);
        if(currentAxioms == null) {
            currentAxioms = DefaultImmutableSet.<ClassAxiom>nil();
        }
        axioms.put(kjt, currentAxioms.add(ax));
    }
    
    
    /**
     * Registers the passed class axioms.
     */
    public void addClassAxioms(ImmutableSet<ClassAxiom> toAdd) {
        for(ClassAxiom ax : toAdd) {
            addClassAxiom(ax);
        }
    }    
    
    
    /**
     * Returns all proofs registered for the passed PO (or stronger POs).
     */
    public ImmutableSet<Proof> getProofs(ProofOblInput po) {
        ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
        	: proofs.entrySet()) {
            ProofOblInput mapPO = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(mapPO.implies(po)) {
                result = result.union(sop);
            }
        }
        return result;
    }
    
    
    /**
     * Returns all proofs registered for the passed operation.
     */
    public ImmutableSet<Proof> getProofs(ProgramMethod pm) {
        ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
        	: proofs.entrySet()) {
            ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(po instanceof ContractPO 
               && ((ContractPO) po).getContract()
                                   .getProgramMethod().equals(pm)) {
                result = result.union(sop);
            }
        }
        return result;
    }
    
    
    /**
     * Returns all proofs registered with this specification repository.
     */
    public ImmutableSet<Proof> getAllProofs() {
	ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
	Collection<ImmutableSet<Proof>> proofSets = proofs.values();
	for(ImmutableSet<Proof> proofSet : proofSets) {
	    result = result.union(proofSet);
	}
	return result;
    }
    
    
    /**
     * Returns the operation that the passed proof is about, or null.
     */
    public ProgramMethod getOperationForProof(Proof proof) {
	for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
		: proofs.entrySet()) {
	    ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(sop.contains(proof) && po instanceof ContractPO) {
                return ((ContractPO)po).getContract().getProgramMethod();
            }
        }
        return null;
    }
    

    /**
     * Registers the passed proof. 
     */
    public void registerProof(ProofOblInput po, Proof proof) {
        proofs.put(po, getProofs(po).add(proof));
    }    
    
    
    /**
     * Unregisters the passed proof.
     */
    public void removeProof(Proof proof) {
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
        	: proofs.entrySet()) {
            ImmutableSet<Proof> sop = (ImmutableSet<Proof>) entry.getValue();
            if(sop.contains(proof)) {
                sop = sop.remove(proof);
                if(sop.size()==0){
                    proofs.remove(entry.getKey());
                }else{
                    proofs.put(entry.getKey(), sop);
                }
                return;
            }
        }
    }
        
    
    /**
     * Returns the registered loop invariant for the passed loop, or null.
     */
    public LoopInvariant getLoopInvariant(LoopStatement loop) {
        return loopInvs.get(loop);
    }


    /**
     * Registers the passed loop invariant, possibly overwriting an older
     * registration for the same loop.
     */
    public void setLoopInvariant(LoopInvariant inv) {
        LoopStatement loop = inv.getLoop();
        loopInvs.put(loop, inv);
    }
    
    
    public void addSpecs(ImmutableSet<SpecificationElement> specs) {
	for(SpecificationElement spec : specs) {
	    if(spec instanceof OperationContract) {
		addOperationContract((OperationContract)spec);
	    } else if(spec instanceof DependencyContract) {
		addDependencyContract((DependencyContract)spec);
	    } else if(spec instanceof ClassInvariant) {
		addClassInvariant((ClassInvariant)spec);
	    } else if(spec instanceof ClassAxiom) {
		addClassAxiom((ClassAxiom)spec);
	    } else if(spec instanceof LoopInvariant) {
		setLoopInvariant((LoopInvariant)spec);
	    } else {
		assert false : "unexpected spec: " + spec;
	    }
	}
    }
}
