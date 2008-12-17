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

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.SetAsListOfProof;
import de.uka.ilkd.key.proof.SetOfProof;
import de.uka.ilkd.key.proof.init.EnsuresPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetAsListOfClassInvariant;
import de.uka.ilkd.key.speclang.SetAsListOfOperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;
import de.uka.ilkd.key.speclang.SetOfOperationContract;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;


public class SpecificationRepository {
    
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    
    private final Map<ProgramMethod, SetOfOperationContract> contracts 
    		= new LinkedHashMap<ProgramMethod,SetOfOperationContract>();
    private final Map<String, OperationContract> contractsByName
                = new LinkedHashMap<String,OperationContract>();
    private final Map<KeYJavaType,SetOfClassInvariant> invs
    		= new LinkedHashMap<KeYJavaType, SetOfClassInvariant>();
    private final Map<String,ClassInvariant> invsByName
                = new LinkedHashMap<String, ClassInvariant>();
    private final Map<KeYJavaType, SetOfClassInvariant> throughoutInvs
    		= new LinkedHashMap<KeYJavaType, SetOfClassInvariant>();
    private final Map<String,ClassInvariant> throughoutInvsByName
                = new LinkedHashMap<String,ClassInvariant>();
    private final Map<ProofOblInput,SetOfProof> proofs
                = new LinkedHashMap<ProofOblInput,SetOfProof>();
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
    public SetOfOperationContract getOperationContracts(ProgramMethod pm) {
	SetOfOperationContract result = contracts.get(pm);
        return result == null ? SetAsListOfOperationContract.EMPTY_SET : result;
    }
    
    
    /**
     * Returns all registered (atomic) contracts for the passed operation which 
     * refer to the passed modality.
     */
    public SetOfOperationContract getOperationContracts(ProgramMethod pm, 
	    						Modality modality) {
	SetOfOperationContract result = getOperationContracts(pm);
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
        SetOfOperationContract baseContracts 
            = SetAsListOfOperationContract.EMPTY_SET;
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
    public void addOperationContracts(SetOfOperationContract contracts) {
        for(OperationContract contract : contracts) {
            addOperationContract(contract);
        }
    }
    
    
    /**
     * Creates a combined contract out of the passed atomic contracts.
     */
    public OperationContract combineContracts(
                                        SetOfOperationContract contracts) {
        assert contracts != null && contracts.size() > 0;
        for(OperationContract contract : contracts) {            
            assert !contract.getName().contains(CONTRACT_COMBINATION_MARKER)
                   : "Please combine only atomic contracts!";
        }

        //sort contracts alphabetically (for determinism)
        OperationContract[] contractsArray = contracts.toArray();
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
            nameSB.append(CONTRACT_COMBINATION_MARKER + other.getName());
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
    public SetOfOperationContract splitContract(OperationContract contract) {
        SetOfOperationContract result = SetAsListOfOperationContract.EMPTY_SET;
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
    public SetOfClassInvariant getClassInvariants(KeYJavaType kjt) {
	SetOfClassInvariant result = invs.get(kjt);
	return result == null ? SetAsListOfClassInvariant.EMPTY_SET : result;
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
    public void addClassInvariants(SetOfClassInvariant invs) {
        for(ClassInvariant inv : invs) {
            addClassInvariant(inv);
        }
    }
    
    
    /**
     * Returns all known throughout invariants for the passed type.
     */
    public SetOfClassInvariant getThroughoutClassInvariants(KeYJavaType kjt) {
	SetOfClassInvariant result = throughoutInvs.get(kjt);
        return result == null ? SetAsListOfClassInvariant.EMPTY_SET : result;
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
    public void addThroughoutClassInvariants(SetOfClassInvariant invs) {
        for(ClassInvariant inv : invs) {
            addThroughoutClassInvariant(inv);
        }
    }
    
    
    /**
     * Returns all proofs registered for the passed PO (or stronger POs).
     */
    public SetOfProof getProofs(ProofOblInput po) {
        SetOfProof result = SetAsListOfProof.EMPTY_SET;
        for(Map.Entry<ProofOblInput,SetOfProof> entry : proofs.entrySet()) {
            ProofOblInput mapPO = entry.getKey();
            SetOfProof sop = entry.getValue();
            if(mapPO.implies(po)) {
                result = result.union(sop);
            }
        }
        return result;
    }
    
    
    /**
     * Returns all proofs registered for the passed operation.
     */
    public SetOfProof getProofs(ProgramMethod pm) {
        SetOfProof result = SetAsListOfProof.EMPTY_SET;
        for(Map.Entry<ProofOblInput,SetOfProof> entry : proofs.entrySet()) {
            ProofOblInput po = entry.getKey();
            SetOfProof sop = entry.getValue();
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
	for(Map.Entry<ProofOblInput,SetOfProof> entry : proofs.entrySet()) {
	    ProofOblInput po = entry.getKey();
            SetOfProof sop = entry.getValue();
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
        for(Map.Entry<ProofOblInput,SetOfProof> entry : proofs.entrySet()) {
            SetOfProof sop = (SetOfProof) entry.getValue();
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
        ListOfParsableVariable paramVars 
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
