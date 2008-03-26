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
import de.uka.ilkd.key.proof.init.EnsuresPostPO;
import de.uka.ilkd.key.proof.init.PreservesInvPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.RespectsModifiesPO;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetAsListOfClassInvariant;
import de.uka.ilkd.key.speclang.SetAsListOfOperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;
import de.uka.ilkd.key.speclang.SetOfOperationContract;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;


public class SpecificationRepository {
    
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
    private final Map<EnsuresPO,SetOfProof> proofs
                = new LinkedHashMap<EnsuresPO,SetOfProof>();
    private final Map<LoopStatement,LoopInvariant> loopInvs
                = new LinkedHashMap<LoopStatement,LoopInvariant>();
    private final Map<ProgramMethod,Boolean> strictPurityCache
    		= new LinkedHashMap<ProgramMethod,Boolean>();
    private final Services services;
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 

    public SpecificationRepository(Services services) {
	this.services = services;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    public SetOfOperationContract getOperationContracts(ProgramMethod pm) {
	SetOfOperationContract result = contracts.get(pm);
        return result == null ? SetAsListOfOperationContract.EMPTY_SET : result;
    }
    
    
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
    

    public OperationContract getOperationContractByName(String name) {
        return contractsByName.get(name);
    }
    
        
    public SetOfClassInvariant getClassInvariants(KeYJavaType kjt) {
	SetOfClassInvariant result = invs.get(kjt);
	return result == null ? SetAsListOfClassInvariant.EMPTY_SET : result;
    }
    

    public ClassInvariant getClassInvariantByName(String name) {
        return invsByName.get(name);
    }
    
    
    public SetOfClassInvariant getThroughoutClassInvariants(KeYJavaType kjt) {
	SetOfClassInvariant result = throughoutInvs.get(kjt);
        return result == null ? SetAsListOfClassInvariant.EMPTY_SET : result;
    }
    
    public ClassInvariant getThroughoutClassInvariantByName(String name) {
        return throughoutInvsByName.get(name);
    }
    
    
    public SetOfProof getProofs(ProofOblInput po) {
        SetOfProof result = proofs.get(po);
        return result == null ? SetAsListOfProof.EMPTY_SET : result; 
    }
    
    
    public SetOfProof getProofs(ProgramMethod pm) {
        SetOfProof result = SetAsListOfProof.EMPTY_SET;
        for(Map.Entry<EnsuresPO,SetOfProof> entry : proofs.entrySet()) {
            EnsuresPO po   = entry.getKey();
            SetOfProof sop = entry.getValue();
            if(po.getProgramMethod().equals(pm)) {
                result = result.union(sop);
            }
        }
        return result;
    }
    
    
    public ProgramMethod getOperationForProof(Proof proof) {
	for(Map.Entry<EnsuresPO,SetOfProof> entry : proofs.entrySet()) {
            EnsuresPO po = entry.getKey();
            SetOfProof sop = entry.getValue();
            if(sop.contains(proof)) {
                return po.getProgramMethod();
            }
        }
        return null;
    }
    
    
    public LoopInvariant getLoopInvariant(LoopStatement loop) {
        return loopInvs.get(loop);
    }

        
    public void addOperationContract(OperationContract contract) {
	ProgramMethod pm = contract.getProgramMethod();
        String name = contract.getName();
        assert contractsByName.get(name) == null 
               : "Tried to add a contract with a non-unique name!";
        contracts.put(pm, getOperationContracts(pm).add(contract));
        contractsByName.put(name, contract);
    }
    
    
    public void addOperationContracts(SetOfOperationContract contracts) {
	for(OperationContract contract : contracts) {
            addOperationContract(contract);
        }
    }
    
    
    public void addClassInvariant(ClassInvariant inv) {
	KeYJavaType kjt = inv.getKJT();
        String name = inv.getName();
        assert invsByName.get(name) == null
               : "Tried to add an invariant with a non-unique name!";
	invs.put(kjt, getClassInvariants(kjt).add(inv));
        invsByName.put(name, inv);
    }
    
    
    public void addClassInvariants(SetOfClassInvariant invs) {
	for(ClassInvariant inv : invs) {
            addClassInvariant(inv);
        }
    }
    
    
    public void addThroughoutClassInvariant(ClassInvariant inv) {
	KeYJavaType kjt = inv.getKJT();
        String name = inv.getName();
        assert throughoutInvsByName.get(name) == null
               : "Tried to add an invariant with a non-unique name!";
	throughoutInvs.put(kjt, getThroughoutClassInvariants(kjt).add(inv));
        throughoutInvsByName.put(name, inv);
    }
    
    
    public void addThroughoutClassInvariants(SetOfClassInvariant invs) {
	for(ClassInvariant inv : invs) {
            addThroughoutClassInvariant(inv);
        }
    }
    
    
    public void registerProof(ProofOblInput po, Proof proof) {
        if(po instanceof EnsuresPostPO 
           || po instanceof PreservesInvPO 
           || po instanceof RespectsModifiesPO) {
            proofs.put((EnsuresPO) po, getProofs(po).add(proof));
        }
    }    
    
    
    public void removeProof(Proof proof) {
	for(Map.Entry<EnsuresPO,SetOfProof> entry : proofs.entrySet()) {
            SetOfProof sop = (SetOfProof) entry.getValue();
            if(sop.contains(proof)) {
                proofs.put(entry.getKey(), sop.remove(proof));
                return;
            }
        }
    }
    
    
    public void setLoopInvariant(LoopInvariant inv) {
        LoopStatement loop = inv.getLoop();
        loopInvs.put(loop, inv);
    }
    
    
    
    public boolean isStrictlyPure(ProgramMethod pm) {
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
