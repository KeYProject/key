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

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.EnsuresPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;


public class SpecificationRepository {
    
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    
    private final Map<ProgramMethod, ImmutableSet<OperationContract>> contracts 
    		= new LinkedHashMap<ProgramMethod,ImmutableSet<OperationContract>>();
    private final Map<String, OperationContract> contractsByName
                = new LinkedHashMap<String,OperationContract>();
    private final Map<KeYJavaType,ImmutableSet<ClassInvariant>> invs
    		= new LinkedHashMap<KeYJavaType, ImmutableSet<ClassInvariant>>();
    private final Map<String,ClassInvariant> invsByName
                = new LinkedHashMap<String, ClassInvariant>();
    private final Map<KeYJavaType, ImmutableSet<ClassInvariant>> throughoutInvs
    		= new LinkedHashMap<KeYJavaType, ImmutableSet<ClassInvariant>>();
    private final Map<String,ClassInvariant> throughoutInvsByName
                = new LinkedHashMap<String,ClassInvariant>();
    private final Map<ProofOblInput,ImmutableSet<Proof>> proofs
                = new LinkedHashMap<ProofOblInput,ImmutableSet<Proof>>();
    private final Map<LoopStatement,LoopInvariant> loopInvs
                = new LinkedHashMap<LoopStatement,LoopInvariant>();
    private final Map<ProgramMethod,Boolean> strictPurityCache
    		= new LinkedHashMap<ProgramMethod,Boolean>();
    private final Services services;
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 

    public SpecificationRepository(Services services) {
	this.services = services;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    /**
     * Returns all registered (atomic) contracts for the passed operation.
     */
    public ImmutableSet<OperationContract> getOperationContracts(ProgramMethod pm) {
	ImmutableSet<OperationContract> result = contracts.get(pm);
        return result == null ? DefaultImmutableSet.<OperationContract>nil() : result;
    }
    
    
    /**
     * Returns all registered (atomic) contracts for the passed operation which 
     * refer to the passed modality.
     */
    public ImmutableSet<OperationContract> getOperationContracts(ProgramMethod pm, 
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
     * Registers the passed (atomic) operation contract, whose name must
     * be different from all previously registered contracts.
     */
    public void addOperationContract(OperationContract contract) {
        ProgramMethod pm = contract.getProgramMethod();
        String name = contract.getName();
        assert contractsByName.get(name) == null 
               : "Tried to add a contract with a non-unique name!";
        assert !name.contains(CONTRACT_COMBINATION_MARKER)
               : "Tried to add a contract with a name containing the reserved" 
                  + " character " + CONTRACT_COMBINATION_MARKER + "!";
        contracts.put(pm, getOperationContracts(pm).add(contract));
        contractsByName.put(name, contract);
    }
    
    
    /**
     * Registers the passed contracts.
     */
    public void addOperationContracts(ImmutableSet<OperationContract> contracts) {
        for(OperationContract contract : contracts) {
            addOperationContract(contract);
        }
    }
    
    
    /**
     * Creates a combined contract out of the passed atomic contracts.
     */
    public OperationContract combineContracts(
                                        ImmutableSet<OperationContract> contracts) {
        assert contracts != null && contracts.size() > 0;
        for(OperationContract contract : contracts) {            
            assert !contract.getName().contains(CONTRACT_COMBINATION_MARKER)
                   : "Please combine only atomic contracts!";
        }

        //sort contracts alphabetically (for determinism)
        OperationContract[] contractsArray = contracts.toArray(new OperationContract[contracts.size()]);
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
        StringBuffer displayNameSB = new StringBuffer(contract.getDisplayName());
        for(OperationContract other : others) {
            nameSB.append(CONTRACT_COMBINATION_MARKER).append(other.getName());
            displayNameSB.append(", ").append(other.getDisplayName());
        }
        
        return contract.union(
                others, 
                nameSB.toString(), 
                (others.length > 0 ? "Combined Contract: " : "") + displayNameSB, 
                services);
    }
    
    
    /**
     * Splits the passed contract into its atomic components. 
     */
    public ImmutableSet<OperationContract> splitContract(OperationContract contract) {
        ImmutableSet<OperationContract> result = DefaultImmutableSet.<OperationContract>nil();
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
    
        
    /**
     * Returns all known class invariants for the passed type.
     */
    public ImmutableSet<ClassInvariant> getClassInvariants(KeYJavaType kjt) {
	ImmutableSet<ClassInvariant> result = invs.get(kjt);
	return result == null ? DefaultImmutableSet.<ClassInvariant>nil() : result;
    }
    

    /**
     * Returns the known class invariant corresponding to the passed name, 
     * or null.
     */
    public ClassInvariant getClassInvariantByName(String name) {
        return invsByName.get(name);
    }
    

    /**
     * Registers the passed class invariant, whose name must be different from 
     * all previously registered class invariants.
     */
    public void addClassInvariant(ClassInvariant inv) {
        KeYJavaType kjt = inv.getKJT();
        String name = inv.getName();
        assert invsByName.get(name) == null
               : "Tried to add an invariant with a non-unique name!";
        invs.put(kjt, getClassInvariants(kjt).add(inv));
        invsByName.put(name, inv);
    }
    
    
    /**
     * Registers the passed class invariants.
     */
    public void addClassInvariants(ImmutableSet<ClassInvariant> invs) {
        for(ClassInvariant inv : invs) {
            addClassInvariant(inv);
        }
    }
    
    
    /**
     * Returns all known throughout invariants for the passed type.
     */
    public ImmutableSet<ClassInvariant> getThroughoutClassInvariants(KeYJavaType kjt) {
	ImmutableSet<ClassInvariant> result = throughoutInvs.get(kjt);
        return result == null ? DefaultImmutableSet.<ClassInvariant>nil() : result;
    }
    
    
    /**
     * Returns the known throughout invariant corresponding to the passed name, 
     * or null.
     */
    public ClassInvariant getThroughoutClassInvariantByName(String name) {
        return throughoutInvsByName.get(name);
    }
    

    /**
     * Registers the passed throughout invariant, whose name must be different 
     * from all previously registered throughout invariants.
     */
    public void addThroughoutClassInvariant(ClassInvariant inv) {
        KeYJavaType kjt = inv.getKJT();
        String name = inv.getName();
        assert throughoutInvsByName.get(name) == null
               : "Tried to add an invariant with a non-unique name!";
        throughoutInvs.put(kjt, getThroughoutClassInvariants(kjt).add(inv));
        throughoutInvsByName.put(name, inv);
    }
    
    
    /**
     * Registers the passed throughout invariants.
     */
    public void addThroughoutClassInvariants(ImmutableSet<ClassInvariant> invs) {
        for(ClassInvariant inv : invs) {
            addThroughoutClassInvariant(inv);
        }
    }
    
    
    /**
     * Returns all proofs registered for the passed PO (or stronger POs).
     */
    public ImmutableSet<Proof> getProofs(ProofOblInput po) {
        ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry : proofs.entrySet()) {
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
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry : proofs.entrySet()) {
            ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(po instanceof EnsuresPO 
               && ((EnsuresPO) po).getProgramMethod().equals(pm)) {
                result = result.union(sop);
            }
        }
        return result;
    }
    
    
    /**
     * Returns the operation that the passed proof is about, or null.
     */
    public ProgramMethod getOperationForProof(Proof proof) {
	for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry : proofs.entrySet()) {
	    ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(sop.contains(proof) && po instanceof EnsuresPO) {
                return ((EnsuresPO)po).getProgramMethod();
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
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry : proofs.entrySet()) {
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
    
    
    /**
     * Tells whether the passed operation is "strictly pure", i.e., whether
     * its specification says that it may have absolutely no side effects
     * (except for abrupt termination, which is not considered a side effect).
     */
    public boolean isStrictlyPure(ProgramMethod pm) {
        assert pm != null;
	Boolean result = strictPurityCache.get(pm);
	if(result != null) {
	    return result;
	}
	
	result = false;
	SignatureVariablesFactory svf = SignatureVariablesFactory.INSTANCE;
	Term tt = TermBuilder.DF.tt();
        ProgramVariable selfVar 
        	= svf.createSelfVar(services, pm, true);
        ImmutableList<ParsableVariable> paramVars 
        	= svf.createParamVars(services, pm, false);
	for(OperationContract c : getOperationContracts(pm, Op.DIA)) {
	    if(c.getPre(selfVar, paramVars, services).getFormula().equals(tt)	   
	       && c.getModifies(selfVar, paramVars, services).size() == 0) {
		result = true;
		break;
	    }
	}
	
	strictPurityCache.put(pm, result);
	return result;
    }
}
