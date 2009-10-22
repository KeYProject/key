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
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Pair;


public final class SpecificationRepository {
    
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final Map<Pair<KeYJavaType,ObserverFunction>, ImmutableSet<Contract>> contracts 
    		= new LinkedHashMap<Pair<KeYJavaType,ObserverFunction>,ImmutableSet<Contract>>();
    private final Map<Pair<KeYJavaType,ProgramMethod>, ImmutableSet<OperationContract>> operationContracts 
    		= new LinkedHashMap<Pair<KeYJavaType,ProgramMethod>,ImmutableSet<OperationContract>>();    
    private final Map<String,Contract> contractsByName
                = new LinkedHashMap<String,Contract>();
    private final Map<KeYJavaType,ImmutableSet<ObserverFunction>> contractTargets
    		= new LinkedHashMap<KeYJavaType,ImmutableSet<ObserverFunction>>();    
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

    private ImmutableSet<Pair<KeYJavaType,ObserverFunction>> 
    		getOverridingMethods(KeYJavaType kjt, ProgramMethod pm) {
        final String name   = pm.getMethodDeclaration().getName();
        final int numParams = pm.getParameterDeclarationCount();
        ImmutableSet<Pair<KeYJavaType,ObserverFunction>> result 
        	= DefaultImmutableSet.<Pair<KeYJavaType,ObserverFunction>>nil();
        
        assert kjt != null;
        final JavaInfo javaInfo = services.getJavaInfo();
        for(KeYJavaType sub : javaInfo.getAllSubtypes(kjt)) {
            assert sub != null;
            
            final ImmutableList<ProgramMethod> subPms 
                = javaInfo.getAllProgramMethods(sub);
            for(ProgramMethod subPm : subPms) {
                if(subPm.getMethodDeclaration().getName().equals(name) 
                   && subPm.getParameterDeclarationCount() == numParams) {
                    boolean paramsEqual = true;
                    for(int i = 0; i < numParams; i++) {
                        if(!subPm.getParameterType(i)
                                 .equals(pm.getParameterType(i))) {
                            paramsEqual = false;
                            break;
                        }
                    }
                    
                    if(paramsEqual) {
                        result = result.add(
                           new Pair<KeYJavaType,ObserverFunction>(sub, subPm));
                        break;
                    }
                }
            }
        }
        
        return result;
    }
    
    
    private ImmutableSet<Pair<KeYJavaType,ObserverFunction>> 
    		getOverridingTargets(KeYJavaType kjt, ObserverFunction target) {
	if(target instanceof ProgramMethod) {
	    return getOverridingMethods(kjt, (ProgramMethod)target);
	} else {
	    ImmutableSet<Pair<KeYJavaType,ObserverFunction>> result 
        	= DefaultImmutableSet.<Pair<KeYJavaType,ObserverFunction>>nil();
	    for(KeYJavaType sub : services.getJavaInfo().getAllSubtypes(kjt)) {
		result = result.add(
			new Pair<KeYJavaType,ObserverFunction>(sub, target));
	    }
	    return result;
	}
    }
    
    
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
     * Returns all registered (atomic) contracts for the passed target.
     */
    public ImmutableSet<Contract> getContracts(KeYJavaType kjt,
	    				       ObserverFunction target) {
	final Pair<KeYJavaType,ObserverFunction> pair 
		= new Pair<KeYJavaType,ObserverFunction>(kjt, target);
	final ImmutableSet<Contract> result = contracts.get(pair);
        return result == null 
               ? DefaultImmutableSet.<Contract>nil() 
               : result;
    }
    
    
    /**
     * Returns all registered (atomic) operation contracts for the passed 
     * operation.
     */
    public ImmutableSet<OperationContract> getOperationContracts(
	    						KeYJavaType kjt, 
	    						ProgramMethod pm) {
	final Pair<KeYJavaType,ProgramMethod> pair 
		= new Pair<KeYJavaType,ProgramMethod>(kjt, pm);
	final ImmutableSet<OperationContract> result 
		= operationContracts.get(pair);
        return result == null 
               ? DefaultImmutableSet.<OperationContract>nil() 
               : result;	
    }
    
    
    /**
     * Returns all registered (atomic) operation contracts for the passed 
     * operation which refer to the passed modality.
     */
    public ImmutableSet<OperationContract> getOperationContracts(
	    				       KeYJavaType kjt,	    
	    				       ProgramMethod pm,
	    				       Modality modality) {
	ImmutableSet<OperationContract> result = getOperationContracts(kjt, pm);
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
    public Contract getContractByName(String name) {
        if(name == null || name.length() == 0) {
            return null;
        }
        
        String[] baseNames = name.split(CONTRACT_COMBINATION_MARKER);
        if(baseNames.length == 1) {
            return contractsByName.get(baseNames[0]);
        }
        
        ImmutableSet<OperationContract> baseContracts 
            = DefaultImmutableSet.<OperationContract>nil();
        for(String baseName : baseNames) {
            OperationContract baseContract 
            	= (OperationContract) contractsByName.get(baseName);
            if(baseContract == null) {
                return null;
            }
            baseContracts = baseContracts.add(baseContract);
        }
        
        return combineOperationContracts(baseContracts);
    }
    
    
    /**
     * Returns a set encompassing the passed contract and all its versions 
     * inherited to overriding methods.
     */
    public ImmutableSet<Contract> getInheritedContracts(Contract contract) {
	ImmutableSet<Contract> result 
		= DefaultImmutableSet.<Contract>nil().add(contract);
        final ImmutableSet<Pair<KeYJavaType,ObserverFunction>> subs 
        	= getOverridingTargets(contract.getKJT(), contract.getTarget());
        for(Pair<KeYJavaType,ObserverFunction> sub : subs) {
            for(Contract subContract : getContracts(sub.first, sub.second)) {
        	if(subContract.id() == contract.id()) {
        	    result = result.add(subContract);
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
    public ImmutableSet<Contract> getInheritedContracts(
	    			ImmutableSet<Contract> contractSet) {
	ImmutableSet<Contract> result = DefaultImmutableSet.<Contract>nil();
        for(Contract c : contractSet) {
            result = result.union(getInheritedContracts(c));
        }
        return result;
    }
    
    
    /**
     * Returns all functions for which contracts are registered in the passed
     * type.
     */
    public ImmutableSet<ObserverFunction> getContractTargets(KeYJavaType kjt) {
	final ImmutableSet<ObserverFunction> result = contractTargets.get(kjt);
        return result == null 
               ? DefaultImmutableSet.<ObserverFunction>nil() 
               : result;
    }
        
    
    /**
     * Registers the passed (atomic) contract, and inherits it to all
     * overriding methods.
     */
    public void addContract(Contract contract) {
	//set id
	contract = contract.setID(contractCounter++);

	//register and inherit
        final ImmutableSet<Pair<KeYJavaType,ObserverFunction>> impls 
        	= getOverridingTargets(contract.getKJT(), contract.getTarget())
        	  .add(new Pair<KeYJavaType,ObserverFunction>(contract.getKJT(),
        		        		              contract.getTarget()));
        
        for(Pair<KeYJavaType,ObserverFunction> impl : impls) {
            contract = contract.setTarget(impl.first, impl.second, services);
            assert contractsByName.get(contract.getName()) == null
                   : "Tried to add a contract with a non-unique name!";
            assert !contract.getName().contains(CONTRACT_COMBINATION_MARKER)
                   : "Tried to add a contract with a name containing the"
                     + " reserved character " 
                     + CONTRACT_COMBINATION_MARKER 
                     + "!";
            assert contract.id() != Contract.INVALID_ID
                   : "Tried to add a contract with an invalid id!";
            contracts.put(impl, 
        	          getContracts(impl.first, impl.second).add(contract));
            if(contract instanceof OperationContract) {
        	operationContracts.put(new Pair<KeYJavaType,ProgramMethod>(impl.first, (ProgramMethod)impl.second), 
        		               getOperationContracts(impl.first, 
        		        	                     (ProgramMethod)impl.second)
        		        	              .add((OperationContract)contract));
            }
            contractsByName.put(contract.getName(), contract);
            contractTargets.put(impl.first, 
                                getContractTargets(impl.first).add(impl.second));
        }
    }
    
    
    /**
     * Registers the passed contracts.
     */
    public void addContracts(ImmutableSet<Contract> toAdd) {
        for(Contract contract : toAdd) {
            addContract(contract);
        }
    }
    
        
    
    /**
     * Creates a combined contract out of the passed atomic contracts.
     */
    public OperationContract combineOperationContracts(
                                    ImmutableSet<OperationContract> toCombine) {
        assert toCombine != null && toCombine.size() > 0;
        for(Contract contract : toCombine) {            
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
    public ImmutableSet<Contract> splitContract(Contract contract) {
        ImmutableSet<Contract> result 
        	= DefaultImmutableSet.<Contract>nil();
        String[] atomicNames 
            = contract.getName().split(CONTRACT_COMBINATION_MARKER);
        for(String atomicName : atomicNames) {
            Contract atomicContract = contractsByName.get(atomicName);
            if(atomicContract == null) {
                return null;
            }
            assert atomicContract.getTarget().equals(contract.getTarget());
            result = result.add(atomicContract);
        }
        return result;
    }
    
        
    /**
     * Registers the passed class invariant, and inherits it to all
     * subclasses.
     */
    public void addClassInvariant(ClassInvariant inv) {
        final KeYJavaType kjt = inv.getKJT();
        invs.put(kjt, getClassInvariants(kjt).add(inv));
        
        if(!inv.isStatic()) {
            final ImmutableList<KeYJavaType> subs 
            	= services.getJavaInfo().getAllSubtypes(kjt);
            for(KeYJavaType sub : subs) {
        	ClassInvariant subInv = inv.setKJT(sub);
        	invs.put(sub, getClassInvariants(sub).add(subInv));
            }
        }
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
	final ImmutableSet<ClassInvariant> myInvs = getClassInvariants(kjt);
	final ProgramVariable selfVar = TB.selfVar(services, kjt, false);
	Term invDef = TB.tt();
	for(ClassInvariant inv : myInvs) {
	    invDef = TB.and(invDef, inv.getInv(selfVar, services));
	}
	invDef = TB.tf().createTerm(Equality.EQV, 
		                    TB.inv(services, TB.var(selfVar)), 
		                    invDef);
	final ObserverFunction invSymbol = services.getJavaInfo().getInv();
	final ClassAxiom invAxiom 
		= new ClassAxiomImpl("Class invariant axiom for " 
			                 + kjt.getFullName(),
				     kjt,		
				     invSymbol,
				     invDef,
				     selfVar);
	result = result.add(invAxiom);
	
	//add query axioms
	for(ProgramMethod pm : services.getJavaInfo()
		                       .getAllProgramMethods(kjt)) {
	    if(pm.getKeYJavaType() != null) {
		pm = services.getJavaInfo().getToplevelPM(kjt, pm);		
		final ClassAxiom queryAxiom 
		    = new QueryClassAxiom("Query axiom for " + pm.getFullName(),
			                  kjt, 
			                  pm);
		result = result.add(queryAxiom);
	    }
	}
	
	//add axioms for enclosing class, if applicable
	final ProgramVariable et 
		= services.getJavaInfo().getAttribute(
			    ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, kjt);
	if(et != null){
	    final KeYJavaType enclosingKJT = et.getKeYJavaType();
	    result = result.union(getClassAxioms(enclosingKJT));
	}
	
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
     * Returns all proofs registered for the passed target and its overriding
     * targets.
     */
    public ImmutableSet<Proof> getProofs(KeYJavaType kjt, 
	    				 ObserverFunction target) {
	final ImmutableSet<Pair<KeYJavaType,ObserverFunction>> targets 
		= getOverridingTargets(kjt, target)
		  .add(new Pair<KeYJavaType,ObserverFunction>(kjt, target));
        ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
        	: proofs.entrySet()) {
            final ProofOblInput po = entry.getKey();
            final ImmutableSet<Proof> sop = entry.getValue();
            if(po instanceof ContractPO) {
               final Contract contract = ((ContractPO) po).getContract();
               final Pair<KeYJavaType,ObserverFunction> pair 
               	    = new Pair<KeYJavaType,ObserverFunction>(
               		    		contract.getKJT(),
               		                contract.getTarget());
               if(targets.contains(pair)) {
        	   result = result.union(sop);
               }
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
     * Returns the target that the passed proof is about, or null.
     */
    public ObserverFunction getTargetOfProof(Proof proof) {
	for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
		: proofs.entrySet()) {
	    ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(sop.contains(proof) && po instanceof ContractPO) {
                return ((ContractPO)po).getContract().getTarget();
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
	    if(spec instanceof Contract) {
		addContract((Contract)spec);
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
