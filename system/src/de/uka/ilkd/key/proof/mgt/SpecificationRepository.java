// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


/**
 * Central storage for all specification elements, such as contracts, class 
 * axioms, and loop invariants. Provides methods for adding such elements to the
 * repository, and for retrieving them afterwards.
 */
public final class SpecificationRepository {
    
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final Map<Pair<KeYJavaType,ObserverFunction>, ImmutableSet<Contract>> contracts 
    		= new LinkedHashMap<Pair<KeYJavaType,ObserverFunction>,ImmutableSet<Contract>>();
    private final Map<Pair<KeYJavaType,ProgramMethod>, ImmutableSet<FunctionalOperationContract>> operationContracts 
    		= new LinkedHashMap<Pair<KeYJavaType,ProgramMethod>,ImmutableSet<FunctionalOperationContract>>();    
    private final Map<String,Contract> contractsByName
                = new LinkedHashMap<String,Contract>();
    private final Map<KeYJavaType,ImmutableSet<ObserverFunction>> contractTargets
    		= new LinkedHashMap<KeYJavaType,ImmutableSet<ObserverFunction>>();    
    private final Map<KeYJavaType,ImmutableSet<ClassInvariant>> invs
    		= new LinkedHashMap<KeYJavaType, ImmutableSet<ClassInvariant>>(); 
    private final Map<KeYJavaType,ImmutableSet<ClassAxiom>> axioms
    		= new LinkedHashMap<KeYJavaType, ImmutableSet<ClassAxiom>>();
    private final Map<KeYJavaType,ImmutableSet<InitiallyClause>> initiallyClauses
            = new LinkedHashMap<KeYJavaType, ImmutableSet<InitiallyClause>>();
    private final Map<ProofOblInput,ImmutableSet<Proof>> proofs
                = new LinkedHashMap<ProofOblInput,ImmutableSet<Proof>>();
    private final Map<LoopStatement,LoopInvariant> loopInvs
                = new LinkedHashMap<LoopStatement,LoopInvariant>();
    private final Map<ObserverFunction,ObserverFunction> unlimitedToLimited
    		= new LinkedHashMap<ObserverFunction,ObserverFunction>();
    private final Map<ObserverFunction,ObserverFunction> limitedToUnlimited
		= new LinkedHashMap<ObserverFunction,ObserverFunction>();
    private final Map<ObserverFunction,ImmutableSet<Taclet>> unlimitedToLimitTaclets
		= new LinkedHashMap<ObserverFunction,ImmutableSet<Taclet>>();
    private final Services services;
    
    private int contractCounter = 0;
    private int libraryContractCounter = -1;
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 

    public SpecificationRepository(Services services) {
	this.services = services;
    }
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private ObserverFunction getCanonicalFormForKJT(ObserverFunction obs, 
	    				            KeYJavaType kjt) {
	assert obs != null;
	assert kjt != null;
	if(!(obs instanceof ProgramMethod) || obs.getContainerType().equals(kjt)) {
	    return unlimitObs(obs);
	}
	final ProgramMethod pm = (ProgramMethod) obs;
	if(pm.isConstructor()) {
	    assert pm.getContainerType().equals(kjt);
	    return pm;
	}
	
	//search through all locally available methods
        final String name   = pm.getMethodDeclaration().getName();
        final int numParams = pm.getParameterDeclarationCount();
	final ImmutableList<ProgramMethod> candidatePMs 
		= services.getJavaInfo().getAllProgramMethods(kjt);
	outer: for(ProgramMethod candidatePM : candidatePMs) {
	    if(candidatePM.getMethodDeclaration().getName().equals(name) 
	       && candidatePM.getParameterDeclarationCount() == numParams) {
		for(int i = 0; i < numParams; i++) {
		    if(!candidatePM.getParameterType(i)
			           .equals(pm.getParameterType(i))) {
			continue outer;
		    }
		}
		return candidatePM;
	    }
	}
	
	//not found (happens for private methods of superclasses) 
	//-> search through superclasses
	for(KeYJavaType sup : services.getJavaInfo()
		                      .getAllSupertypes(kjt)
		                      .removeAll(kjt)) {
	    final ProgramMethod result 
	    	= (ProgramMethod) getCanonicalFormForKJT(obs, sup);
	    if(result != null) {
		return result;
	    }
	}
	
	//should not happen
	assert false : "Could not find method " 
	               + pm.getName() + " in type " + kjt;
	return null;
    }
    

    private ImmutableSet<Pair<KeYJavaType,ObserverFunction>> 
    		getOverridingMethods(KeYJavaType kjt, ProgramMethod pm) {
        ImmutableSet<Pair<KeYJavaType,ObserverFunction>> result 
        	= DefaultImmutableSet.<Pair<KeYJavaType,ObserverFunction>>nil();
        
        if(pm.isConstructor()) {
            return result;
        }
        
        assert kjt != null;
        final JavaInfo javaInfo = services.getJavaInfo();
        for(KeYJavaType sub : javaInfo.getAllSubtypes(kjt)) {
            assert sub != null;
            final ProgramMethod subPM 
            	= (ProgramMethod) getCanonicalFormForKJT(pm, sub);
            result = result.add(new Pair<KeYJavaType,ObserverFunction>(sub, 
        	    						       subPM));
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
    
    
    /**
     * Returns the kjt for the outer class, if the passed kjt is a member class,
     * and null otherwise.
     */
    private KeYJavaType getEnclosingKJT(KeYJavaType kjt) {
	//HACK, this should be easier
	if(kjt.getJavaType() instanceof ClassDeclaration) {
	    final String name = kjt.getJavaType().getFullName();
	    if(name.contains(".")) {
		final String enclosingName 
			= name.substring(0, name.lastIndexOf("."));
		final KeYJavaType result 
			= services.getJavaInfo().getKeYJavaType(enclosingName);
		return result;
	    } else {
		return null;
	    }
	} else {
	    return null;
	}
    }
    
    
    private boolean axiomIsVisible(ClassAxiom ax, KeYJavaType visibleTo) {
        final KeYJavaType kjt = ax.getKJT();
        //TODO: package information not yet available
        // DISCUSSION: how should it be treated in the mean time? as public? Our specifications rarely stretch over different packages... 
        final boolean visibleToPackage = true;
        final VisibilityModifier visibility = ax.getVisibility();
        if (VisibilityModifier.isPublic(visibility))
            return true;
        if (VisibilityModifier.allowsInheritance(visibility))
            return visibleTo.getSort().extendsTrans(kjt.getSort()) || visibleToPackage;
        if (VisibilityModifier.isPackageVisible(visibility))
            return visibleToPackage;
        else
            return kjt.equals(visibleTo);
    }
    
    private ImmutableSet<ClassAxiom> getVisibleAxiomsOfOtherClasses(
	    						KeYJavaType visibleTo) {
	ImmutableSet<ClassAxiom> result = DefaultImmutableSet.<ClassAxiom>nil();
	for(Map.Entry<KeYJavaType, ImmutableSet<ClassAxiom>> e 
							: axioms.entrySet()) {
	    if(e.getKey().equals(visibleTo)) {
		continue;
	    }
	    for(ClassAxiom ax : e.getValue()) {
		if(axiomIsVisible(ax, visibleTo)) {
		    result = result.add(ax);
		}
	    }
	}
	return result;
    }
    
    
    private static Taclet getLimitedToUnlimitedTaclet(
	    				ObserverFunction limited, 
	    				ObserverFunction unlimited) {
	assert limited.arity() == unlimited.arity();
	
	//create schema terms
	final Term[] subs = new Term[limited.arity()]; 
	for(int i = 0; i < subs.length; i++) {
	    final SchemaVariable argSV 
	    	= SchemaVariableFactory.createTermSV(new Name("t" + i), 
	    					     limited.argSort(i), 
	    					     false, 
	    					     false);
	    subs[i] = TB.var(argSV);
	}
	final Term limitedTerm = TB.func(limited, subs);
	final Term unlimitedTerm = TB.func(unlimited, subs);	
	
	//create taclet
	final RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
	tacletBuilder.setFind(limitedTerm);
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
					   ImmutableSLList.<Taclet>nil(),
					   unlimitedTerm));
	tacletBuilder.setName(MiscTools.toValidTacletName(
					"unlimit " + unlimited.name()));
	
	return tacletBuilder.getTaclet();
    }
    
    
    private static Taclet getUnlimitedToLimitedTaclet(
					ObserverFunction limited, 
					ObserverFunction unlimited) {
	assert limited.arity() == unlimited.arity();
	
	//create schema terms
	final Term[] subs = new Term[limited.arity()]; 
	for(int i = 0; i < subs.length; i++) {
	    final SchemaVariable argSV 
	    	= SchemaVariableFactory.createTermSV(new Name("t" + i), 
	    					     limited.argSort(i), 
	    					     false, 
	    					     false);
	    subs[i] = TB.var(argSV);
	}
	final Term limitedTerm = TB.func(limited, subs);
	final Term unlimitedTerm = TB.func(unlimited, subs);
	
	//create taclet
	final RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
	tacletBuilder.setFind(TB.func(unlimited, subs));
	final SequentFormula cf 
		= new SequentFormula(TB.equals(limitedTerm, unlimitedTerm));
	final Sequent addedSeq 
		= Sequent.createAnteSequent(Semisequent.EMPTY_SEMISEQUENT
			                               .insertFirst(cf)
			                               .semisequent());
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(addedSeq,
					   ImmutableSLList.<Taclet>nil(),
					   TB.func(unlimited, subs)));
	tacletBuilder.setStateRestriction(RewriteTaclet.IN_SEQUENT_STATE);
	tacletBuilder.setName(MiscTools.toValidTacletName(
					"limit " + unlimited.name()));
	tacletBuilder.addRuleSet(new RuleSet(new Name("limitObserver")));
	
	return tacletBuilder.getTaclet();
    }
    
    


    private RepresentsAxiom getRepresentsAxiom (KeYJavaType kjt, ClassAxiom ax){
        if (!(ax instanceof RepresentsAxiom) || axioms.get(kjt)== null)
            return null;
        RepresentsAxiom result = null;
        for (ClassAxiom ca: axioms.get(kjt)){
            if (ca instanceof RepresentsAxiom && (ca.getTarget().equals(ax.getTarget()))){
                assert result == null : "More than one represents clause for "+ax.getTarget();
                result = (RepresentsAxiom)ca;
            }
        }
        return result;
    }
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    /**
     * Returns all registered contracts.
     */
    public ImmutableSet<Contract> getAllContracts() {
	ImmutableSet<Contract> result = DefaultImmutableSet.<Contract>nil();
	for(ImmutableSet<Contract> s : contracts.values()) {
	    result = result.union(s);
	}
	return result;
    }
    
    
    /**
     * Returns all registered (atomic) contracts for the passed target.
     */
    public ImmutableSet<Contract> getContracts(KeYJavaType kjt,
	    				       ObserverFunction target) {
	assert kjt != null;
	assert target != null;
	target = getCanonicalFormForKJT(target, kjt);
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
    public ImmutableSet<FunctionalOperationContract> getOperationContracts(
	    						KeYJavaType kjt, 
	    						ProgramMethod pm) {
	pm = (ProgramMethod) getCanonicalFormForKJT(pm, kjt);
	final Pair<KeYJavaType,ProgramMethod> pair 
		= new Pair<KeYJavaType,ProgramMethod>(kjt, pm);
	final ImmutableSet<FunctionalOperationContract> result 
		= operationContracts.get(pair);
        return result == null 
               ? DefaultImmutableSet.<FunctionalOperationContract>nil() 
               : result;	
    }
    
    
    /**
     * Returns all registered (atomic) operation contracts for the passed 
     * operation which refer to the passed modality.
     */
    public ImmutableSet<FunctionalOperationContract> getOperationContracts(
	    				       KeYJavaType kjt,	    
	    				       ProgramMethod pm,
	    				       Modality modality) {
	ImmutableSet<FunctionalOperationContract> result = getOperationContracts(kjt, pm);
	for(FunctionalOperationContract contract : result) {
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
        
        ImmutableSet<FunctionalOperationContract> baseContracts 
            = DefaultImmutableSet.<FunctionalOperationContract>nil();
        for(String baseName : baseNames) {
            FunctionalOperationContract baseContract 
            	= (FunctionalOperationContract) contractsByName.get(baseName);
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
	//sanity check
	assert getCanonicalFormForKJT(contract.getTarget(), 
		                      contract.getKJT())
	            .equals(contract.getTarget());
	
	//set id
	if(((TypeDeclaration)contract.getKJT().getJavaType()).isLibraryClass()) {
	    contract = contract.setID(libraryContractCounter--);
	    assert libraryContractCounter > Integer.MIN_VALUE : "too many library contracts";
	} else {
	    contract = contract.setID(contractCounter++);
	}
	
	//register and inherit
        final ImmutableSet<Pair<KeYJavaType,ObserverFunction>> impls 
        	= getOverridingTargets(contract.getKJT(), contract.getTarget())
        	  .add(new Pair<KeYJavaType,ObserverFunction>(contract.getKJT(),
        		        		              contract.getTarget()));
        
        for(Pair<KeYJavaType,ObserverFunction> impl : impls) {
            contract = contract.setTarget(impl.first, impl.second, services);
            final String name = contract.getName();
            assert contractsByName.get(name) == null
                   : "Tried to add a contract with a non-unique name: " + name;
            assert !name.contains(CONTRACT_COMBINATION_MARKER)
                   : "Tried to add a contract with a name containing the"
                     + " reserved character " 
                     + CONTRACT_COMBINATION_MARKER 
                     + ": " + name;
            assert contract.id() != Contract.INVALID_ID
                   : "Tried to add a contract with an invalid id!";
            contracts.put(impl, 
        	          getContracts(impl.first, impl.second).add(contract));
            
            if(contract instanceof FunctionalOperationContract) {
        	operationContracts.put(new Pair<KeYJavaType,ProgramMethod>(impl.first, (ProgramMethod)impl.second), 
        		               getOperationContracts(impl.first, 
        		        	                     (ProgramMethod)impl.second)
        		        	              .add((FunctionalOperationContract)contract));
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
    public FunctionalOperationContract combineOperationContracts(
                                    ImmutableSet<FunctionalOperationContract> toCombine) {
        assert toCombine != null && toCombine.size() > 0;
        for(Contract contract : toCombine) {            
            assert !contract.getName().contains(CONTRACT_COMBINATION_MARKER)
                   : "Please combine only atomic contracts!";
        }

        //sort contracts alphabetically (for determinism)
        FunctionalOperationContract[] contractsArray 
        	= toCombine.toArray(new FunctionalOperationContract[toCombine.size()]);
        Arrays.sort(contractsArray, new Comparator<FunctionalOperationContract> () {
            public int compare(FunctionalOperationContract c1, FunctionalOperationContract c2) {
                return c1.getName().compareTo(c2.getName());
            }
        });
        
        //split
        FunctionalOperationContract contract = contractsArray[0];
        FunctionalOperationContract[] others 
            = new FunctionalOperationContract[contractsArray.length - 1];
        System.arraycopy(contractsArray, 
                         1, 
                         others, 
                         0, 
                         contractsArray.length - 1);
        
        //determine names
        StringBuffer nameSB = new StringBuffer(contract.getName());
        for(FunctionalOperationContract other : others) {
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
     * subclasses if it is public or protected.
     */
    public void addClassInvariant(ClassInvariant inv) {
        final KeYJavaType kjt = inv.getKJT();
        invs.put(kjt, getClassInvariants(kjt).add(inv));
        
        addClassAxiom(new PartialInvAxiom(inv, services));
        
        if(!inv.isStatic() && VisibilityModifier.allowsInheritance(inv.getVisibility())) {
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
    
    private void createContractsFromInitiallyClause(InitiallyClause inv, KeYJavaType kjt) {
        if (!kjt.equals(inv.getKJT()))
            inv = inv.setKJT(kjt);
        for (ProgramMethod pm: services.getJavaInfo().getConstructors(kjt)){
            if (!JMLInfoExtractor.isHelper(pm)){
                final ImmutableSet<Contract> iniContr = inv.toContract(pm);
                final ImmutableSet<Contract> oldContracts = getContracts(kjt,pm);
                if (oldContracts.isEmpty()) {
                    // add new contract, TODO: check whether defaults a valid
                    addContracts(iniContr);
                } else {
                    // add initially clause as postcondition to all contracts
                    ImmutableSet<FunctionalOperationContract> funcContracts = DefaultImmutableSet.<FunctionalOperationContract>nil();
                    for (Contract c: iniContr) {
                        if (c instanceof FunctionalOperationContract)
                            funcContracts = funcContracts.add((FunctionalOperationContract)c);
                    }
                    assert funcContracts.size() == 1 : "funcContracts more than 1";
                    final FunctionalOperationContract iniContract = funcContracts.toArray(new FunctionalOperationContract[1])[0];
                    ImmutableSet<Contract> newContracts = DefaultImmutableSet.<Contract>nil();
                    for (Contract c: oldContracts){
                        if (c instanceof FunctionalOperationContract){
                            ImmutableSet<FunctionalOperationContract> tmp = DefaultImmutableSet.<FunctionalOperationContract>nil().add((FunctionalOperationContract)c).add(iniContract);
                            newContracts = newContracts.add(combineOperationContracts(tmp));
                        } else {
                            newContracts = newContracts.add(c);
                        }
                    }
                    contracts.put(new Pair<KeYJavaType, ObserverFunction>(kjt,pm), newContracts);
                }
            }
        }
    }
    public void createContractsFromInitiallyClauses(){
        for (KeYJavaType kjt: initiallyClauses.keySet()){
            for (InitiallyClause inv: initiallyClauses.get(kjt)){
                createContractsFromInitiallyClause(inv,kjt);
                if (VisibilityModifier.allowsInheritance(inv.getVisibility())){
                    final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
                    for (KeYJavaType sub: subs){
                    createContractsFromInitiallyClause(inv,sub);
                    }}
            }
        }
    }
    
    public void addInitiallyClause(InitiallyClause ini){
        ImmutableSet<InitiallyClause> oldClauses = initiallyClauses.get(ini.getKJT());
        if (oldClauses == null)
            oldClauses = DefaultImmutableSet.<InitiallyClause>nil();
        initiallyClauses.put(ini.getKJT(), oldClauses.add(ini));
    }
    
    
    /**
     * Registers the passed initially clauses as new contracts to all constructors of their KJT.
     */
    public void addInitiallyClauses(ImmutableSet<InitiallyClause> toAdd) {
        for(InitiallyClause inv : toAdd) {
            addInitiallyClause(inv);
        }
    }
    
    /**
     * Returns all class axioms visible in the passed class, including
     * the axioms induced by invariant declarations.
     */
    public ImmutableSet<ClassAxiom> getClassAxioms(KeYJavaType kjt) {
	//get visible registered axioms of other classes
	ImmutableSet<ClassAxiom> result = getVisibleAxiomsOfOtherClasses(kjt);	
	
	//add registered axioms of own class
	ImmutableSet<ClassAxiom> ownAxioms = axioms.get(kjt);
	if(ownAxioms != null) {
	    for(ClassAxiom ax : ownAxioms) {
		result = result.add(ax);
	    }
	}
	
	//add invariant axiom for own class
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
	final ClassAxiom invRepresentsAxiom 
		= new RepresentsAxiom("Class invariant axiom for " 
			                 + kjt.getFullName(),
			              invSymbol,
				      kjt,	
				      new Private(),
				      invDef,
				      selfVar);
	result = result.add(invRepresentsAxiom);
		
	//add query axioms for own class
	for(ProgramMethod pm : services.getJavaInfo()
		                       .getAllProgramMethods(kjt)) {
	    if(pm.getKeYJavaType() != null && !pm.isImplicit()) {
		pm = services.getJavaInfo().getToplevelPM(kjt, pm);		
		final ClassAxiom queryAxiom 
		    = new QueryAxiom("Query axiom for " + pm.getName() 
			    	     + " in " + kjt.getFullName(),
			    	     pm, 
			             kjt);
		result = result.add(queryAxiom);
	    }
	}
	//add axioms for enclosing class, if applicable
	final KeYJavaType enclosingKJT = getEnclosingKJT(kjt);
	if(enclosingKJT != null) {
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
        if (ax instanceof RepresentsAxiom) {
            // there may only be one conjoined represents axiom per model field
            RepresentsAxiom  oldRep = getRepresentsAxiom(kjt, ax);
            if (oldRep != null) {
                final RepresentsAxiom newRep = oldRep.conjoin((RepresentsAxiom)ax);
                axioms.put(kjt, currentAxioms.remove(oldRep).add(newRep));
            } else {
                axioms.put(kjt, currentAxioms.add(ax));
            }
            // inherit represents clauses to subclasses and conjoin together
            if (VisibilityModifier.allowsInheritance(ax.getVisibility())){
                final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
                for (KeYJavaType sub: subs){
                    RepresentsAxiom subAx =  ((RepresentsAxiom)ax).setKJT(sub);
                    currentAxioms = axioms.get(sub);
                    if(currentAxioms == null) {
                        currentAxioms = DefaultImmutableSet.<ClassAxiom>nil();
                    }
                    oldRep = getRepresentsAxiom(sub, subAx);
                    if (oldRep == null)
                        axioms.put(sub, currentAxioms.add(subAx));
                    else {
                        final RepresentsAxiom newSubRep = oldRep.conjoin(subAx);
                        axioms.put(sub, currentAxioms.remove(oldRep).add(newSubRep));
                    }
                }}
        } else {
            axioms.put(kjt, currentAxioms.add(ax));
        }
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
     * Returns all proofs registered for the passed atomic contract, or for
     * combined contracts including the passed atomic contract
     */
    public ImmutableSet<Proof> getProofs(Contract atomicContract) {
        assert !atomicContract.getName().contains(CONTRACT_COMBINATION_MARKER)
               : "Contract must be atomic";
	
        ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
               : proofs.entrySet()) {
            final ProofOblInput po = entry.getKey();
            if(po instanceof ContractPO) {
        	final Contract poContract = ((ContractPO)po).getContract();
        	if(splitContract(poContract).contains(atomicContract)) {
        	    result = result.union(entry.getValue());
        	}
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
     * Returns the PO that the passed proof is about, or null.
     */
    public ContractPO getPOForProof(Proof proof) {
	for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
		: proofs.entrySet()) {
	    ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(sop.contains(proof) && po instanceof ContractPO) {
                return (ContractPO)po;
            }
        }
        return null;
    }    
    
    
    /**
     * Returns the target that the passed proof is about, or null.
     */
    public ObserverFunction getTargetOfProof(Proof proof) {
	final ContractPO po = getPOForProof(proof);
	return po == null ? null : po.getContract().getTarget();
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
	    } else if(spec instanceof InitiallyClause){
		addInitiallyClause((InitiallyClause)spec);
	    } else if(spec instanceof ClassAxiom) {
		addClassAxiom((ClassAxiom)spec);
	    } else if(spec instanceof LoopInvariant) {
		setLoopInvariant((LoopInvariant)spec);
	    } else {
		assert false : "unexpected spec: " + spec +"\n("+spec.getClass()+")";
	    }
	}
    }
    
    
    public Pair<ObserverFunction,ImmutableSet<Taclet>> limitObs(
	    					ObserverFunction obs) {
	assert limitedToUnlimited.get(obs) == null 
	       : " observer is already limited: " + obs;
	if(obs.getClass() != ObserverFunction.class) {
	    return null;
	}
	
	ObserverFunction limited = unlimitedToLimited.get(obs);
	ImmutableSet<Taclet> taclets = unlimitedToLimitTaclets.get(obs);
	
	if(limited == null) {
	    final String baseName
	    	= ((ProgramElementName)obs.name()).getProgramName() + "$lmtd";
	    final Sort heapSort
	    	= services.getTypeConverter().getHeapLDT().targetSort();
	    limited = new ObserverFunction(baseName,
		    			   obs.sort(),
		    			   obs.getType(),
		    			   heapSort,	
		    			   obs.getContainerType(),
		    			   obs.isStatic(),
		    			   obs.getParamTypes());
	    unlimitedToLimited.put(obs, limited);
	    limitedToUnlimited.put(limited, obs);
	    
	    assert taclets == null;	    
	    taclets = DefaultImmutableSet
	    			.<Taclet>nil()
	                        .add(getLimitedToUnlimitedTaclet(limited, obs))
	    			.add(getUnlimitedToLimitedTaclet(limited, obs));
	    unlimitedToLimitTaclets.put(obs, taclets);
	}
	
	assert limited != null;
	assert taclets != null;
	return new Pair<ObserverFunction,ImmutableSet<Taclet>>(limited, 
							       taclets);
    }
    
    
    public ObserverFunction unlimitObs(ObserverFunction obs) {
	ObserverFunction result = limitedToUnlimited.get(obs);
	if(result == null) {
	    result = obs;
	}
	return result;
    }
}
