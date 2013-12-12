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


package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;


/**
 * The proof obligation for dependency contracts. 
 */
public final class DependencyContractPO extends AbstractPO 
                                        implements ContractPO {
    
    private Term mbyAtPre;    
    
    private DependencyContract contract;
           
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public DependencyContractPO(InitConfig initConfig, 
	    			DependencyContract contract) {
    	super(initConfig, contract.getName());
    	assert !(contract instanceof FunctionalOperationContract);
      this.contract = contract;
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    
    private Term buildFreePre(
    		              List<LocationVariable> heaps,
    		              Collection<LocationVariable> preHeaps,
    		              ProgramVariable selfVar,
	                      KeYJavaType selfKJT,
	                      ImmutableList<ProgramVariable> paramVars,
	                      Term wellFormedHeaps) 
    		throws ProofInputException {
        //"self != null"
	final Term selfNotNull 
            = selfVar == null
              ? TB.tt()
              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
              
        //"self.<created> = TRUE" for all heaps

        Term selfCreated = null;
        if (selfVar != null) {
            for(LocationVariable h : heaps) {
                final Term sc = TB.created(services, TB.var(h), TB.var(selfVar));
                if (selfCreated == null) {
                    selfCreated = sc;
                }else{
                    selfCreated = TB.and(selfCreated, sc);
                }
            }
            if (preHeaps != null) {
                for(LocationVariable h : preHeaps) {
                    final Term sc = TB.created(services, TB.var(h), TB.var(selfVar));
                    if (selfCreated == null) {
                       selfCreated = sc;
                    } else {
                       selfCreated = TB.and(selfCreated, sc);
                    }
                }
            }
        } else {
            selfCreated = TB.tt();
        }

        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType
           = selfVar == null
             ? TB.tt()
             : TB.exactInstance(services, 
        	                selfKJT.getSort(), 
        	                TB.var(selfVar));


        //conjunction of... 
        //- "p_i = null | p_i.<created> = TRUE" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK = TB.tt();
        for(ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }

        //initial value of measured_by clause
        final Term mbyAtPreDef;
        if (contract.hasMby()) {
/*
            final Function mbyAtPreFunc
            = new Function(new Name(TB.newName(services, "mbyAtPre")),
                            services.getTypeConverter()
                                    .getIntegerLDT()
                                    .targetSort());
            register(mbyAtPreFunc);
            mbyAtPre = TB.func(mbyAtPreFunc);
*/
            final Term mby = contract.getMby(selfVar, paramVars, services);
//            mbyAtPreDef = TB.equals(mbyAtPre, mby);
            mbyAtPreDef = TB.measuredBy(mby, services);
        } else {
//            mbyAtPreDef = TB.tt();
            mbyAtPreDef = TB.measuredByEmpty(services);
        }        
             
        return TB.and(new Term[]{wellFormedHeaps,
        	       		 selfNotNull,
        	       		 selfCreated,
        	       		 selfExactType,
        	       		 paramsOK,
        	       		 mbyAtPreDef});        
    }    
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    
    @Override
    public void readProblem() throws ProofInputException {
        IObserverFunction target = contract.getTarget();
        if(target instanceof IProgramMethod) {
            target = javaInfo.getToplevelPM(contract.getKJT(),
		    			    (IProgramMethod)target);
	    // FIXME: for some reason the above method call returns null now and then, the following line (hopefully) is a work-around
	    if (target == null) target = contract.getTarget();
	}

	//prepare variables
	final ProgramVariable selfVar
                = !contract.getTarget().isStatic() 
                ? TB.selfVar(services, contract.getKJT(), true) : null;
	final ImmutableList<ProgramVariable> paramVars
		= TB.paramVars(services, target, true);

	final boolean twoState = (contract.getTarget().getStateCount() == 2);
	final int heapCount = contract.getTarget().getHeapCount(services);
	
	final Map<LocationVariable,LocationVariable> preHeapVars =
	        new LinkedHashMap<LocationVariable, LocationVariable>();
	final Map<LocationVariable,LocationVariable> preHeapVarsReverse =
	        new LinkedHashMap<LocationVariable, LocationVariable>();
	List<LocationVariable> heaps = new LinkedList<LocationVariable>();
	int hc = 0;
	for(LocationVariable h : HeapContext.getModHeaps(services, false)) {
	    if(hc >= heapCount) {
	        break;
	    }
	    heaps.add(h);
	    LocationVariable preVar = twoState ?
	            TB.heapAtPreVar(services, h.name()+"AtPre", h.sort(), true)
	            : null ;
	    if(preVar != null) { register(preVar); }
	    preHeapVars.put(h, preVar);
	    if(preVar != null) {
	        preHeapVarsReverse.put(preVar, h);
	    }
	}
	if(twoState) {
	    heaps.addAll(preHeapVars.values());
	}

        //register the variables and anon heap so they are declared in proof 
	//header if the proof is saved to a file
        register(selfVar);	
        register(paramVars);

        Term wellFormedHeaps = null;
        Term update = null;
        for(LocationVariable h : heaps) {
            final Term wellFormedHeap = TB.wellFormed(h, services);
            if(wellFormedHeaps == null) {
                wellFormedHeaps = wellFormedHeap;
            } else {
                wellFormedHeaps = TB.and(wellFormedHeaps, wellFormedHeap);
            }
            //prepare anon heap
            final Name anonHeapName = new Name(TB.newName(services, "anon_"+h.toString()));
            final Function anonHeapFunc = new Function(anonHeapName, heapLDT.targetSort());
            register(anonHeapFunc);
            final Term anonHeap = TB.label(TB.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);
            final Term wellFormedAnonHeap = TB.wellFormed(anonHeap, services);
            if(wellFormedHeaps == null) {
                wellFormedHeaps = wellFormedAnonHeap;
            } else {
                wellFormedHeaps = TB.and(wellFormedHeaps,wellFormedAnonHeap);
            }
            //prepare update
            final boolean atPre = preHeapVars.values().contains(h);
            final Term dep = getContract().getDep(atPre ?
                    preHeapVarsReverse.get(h) : h, atPre, selfVar, paramVars, preHeapVars, services);
            final Term changedHeap =
                    TB.anon(services, TB.var(h),
                            TB.setMinus(services, TB.allLocs(services), dep), anonHeap);
            final Term u = TB.elementary(services, h, changedHeap);
            if (update == null) {
                update = u;
            } else {
                update = TB.parallel(update, u);
            }
        }

	//translate contract
	final Term pre = TB.and(
	   buildFreePre(heaps, twoState ? preHeapVars.values() : null, selfVar,
	                contract.getKJT(), paramVars, wellFormedHeaps),
	                contract.getPre(heapLDT.getHeap(), selfVar, paramVars,
	                                null, services));

	assert heaps.size() == heapCount;
	//prepare target term
	final Term[] subs
	    = new Term[paramVars.size() + heaps.size() + (target.isStatic() ? 0 : 1)];
	int offset = 0;
	for(LocationVariable heap : heaps) {
	    subs[offset++] = TB.var(heap);
	}
	if(!target.isStatic()) {
	    subs[offset++] = TB.var(selfVar);
	}
	for(ProgramVariable paramVar : paramVars) {
	    subs[offset++] = TB.var(paramVar);
	}
	final Term targetTerm = TB.func(target, subs);
	
	//build po
	final Term po = TB.imp(pre,
                               TB.equals(targetTerm, 
                        	         TB.apply(update, targetTerm, null)));
	
        //save in field
        assignPOTerms(po);
        
        //add axioms
        collectClassAxioms(contract.getKJT());
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof DependencyContractPO)) {
            return false;
        }
        DependencyContractPO cPO = (DependencyContractPO) po;
        return contract.equals(cPO.contract);
    }
    
    
    @Override
    public DependencyContract getContract() {
        return contract;
    }
    
    
    @Override
    public Term getMbyAtPre() {
	return mbyAtPre;
    }
   
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof DependencyContractPO)) {
	    return false;
	} else {
	    return contract.equals(((DependencyContractPO)o).contract);
	}
    }
    
    
    @Override
    public int hashCode() {
        return contract.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("contract", contract.getName());
    }
    
    /**
     * Instantiates a new proof obligation with the given settings.
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties)
            throws IOException {
        String contractName = properties.getProperty("contract");
        int proofNum = 0;
        String baseContractName = null;
        int ind = -1;
        for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
            ind = contractName.indexOf("." + tag);
            if (ind > 0) {
                break;
            }
            proofNum++;
        }
        if (ind == -1) {
            baseContractName = contractName;
            proofNum = 0;
        }
        else {
            baseContractName = contractName.substring(0, ind);
        }
        final Contract contract = initConfig.getServices()
                .getSpecificationRepository().getContractByName(baseContractName);
        if (contract == null) {
            throw new RuntimeException("Contract not found: " + baseContractName);
        }
        else {
            return new LoadedPOContainer(contract.createProofObl(initConfig, contract), proofNum);
        }
    }
}
