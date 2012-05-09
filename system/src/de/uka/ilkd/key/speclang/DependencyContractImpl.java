// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.DependencyContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Standard implementation of the DependencyContract interface.
 */
public final class DependencyContractImpl implements DependencyContract {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    final String baseName;    
    final String name;
    final KeYJavaType kjt;
    final ObserverFunction target;
    final Term originalPre;
    final Term originalMby;    
    final Term originalDep;
    final ProgramVariable originalSelfVar;
    final ImmutableList<ProgramVariable> originalParamVars;
    final int id;    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    DependencyContractImpl(String baseName,
	                           String name, 
	                           KeYJavaType kjt,
	    			   ObserverFunction target,
	    			   Term pre,
	                  	   Term mby,	    			   
	                  	   Term dep,
	                  	   ProgramVariable selfVar,
	                  	   ImmutableList<ProgramVariable> paramVars,
	                  	   int id) {
	assert baseName != null;
	assert kjt != null;
	assert target != null;
	assert pre != null;
	assert dep != null : "cannot create contract "+baseName+" for "+target+" when no specification is given";
        assert (selfVar == null) == target.isStatic();
        assert paramVars != null;
        assert paramVars.size() == target.arity() - (target.isStatic() ? 1 : 2);
        assert pre.sort() == Sort.FORMULA;
	this.baseName = baseName;
        this.name = name != null 
                  ? name 
                  : ContractFactory.generateContractName(baseName, kjt, target,
                                       id);
	this.kjt = kjt;
	this.target = target;
	this.originalPre = pre;
	this.originalMby = mby;	
	this.originalDep = dep;
	this.originalSelfVar = selfVar;
	this.originalParamVars = paramVars;
	this.id = id;
    }
    
    
    DependencyContractImpl(String baseName, 
	                          KeYJavaType kjt,
	    			  ObserverFunction target,
	    			  Term pre,
	                  	  Term mby,	    			  
	                  	  Term dep,
	                  	  ProgramVariable selfVar,
	                  	  ImmutableList<ProgramVariable> paramVars) {
	this(baseName, 
             null, 
             kjt, 
             target, 
             pre, 
             mby,             
             dep, 
             selfVar, 
             paramVars, 
             INVALID_ID);
    }    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------    
    
    @Override
    public String getName() {
	return name;
    }
    
    
    @Override
    public int id() {
	return id;
    }
    

    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }

    
    @Override
    public ObserverFunction getTarget() {
	return target;
    }
    
    
    @Override
    public boolean hasMby() {
	return originalMby != null;
    }
    
    
    @Override
    public Term getPre(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Map<String, ? extends ProgramVariable> atPreVars,
	    	       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	if (originalSelfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(originalParamVar, paramVars.head());
	    paramVars = paramVars.tail();
	}
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalPre);
    }
    
    
    @Override
    public Term getPre(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Map<String,Term> atPres,
	    	       Services services) {
	assert heapTerm != null;
	assert (selfTerm == null) == (originalSelfVar == null);
	assert paramTerms != null;
	assert paramTerms.size() == originalParamVars.size();
	assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	map.put(TB.heap(TB.BASE_HEAP_NAME, services), heapTerm);
	if (originalSelfVar != null) {
            map.put(TB.var(originalSelfVar), selfTerm);
        }
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(TB.var(originalParamVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}	
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalPre);
    }
    
    

    @Override
    public Term getMby(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services) {
	assert hasMby();
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	if (originalSelfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(originalParamVar, paramVars.head());
	    paramVars = paramVars.tail();
	}
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalMby);
    }
    

    @Override
    public Term getMby(Term heapTerm,
	               Term selfTerm, 
	               ImmutableList<Term> paramTerms, 
	               Services services) {
	assert hasMby();
	assert heapTerm != null;
	assert (selfTerm == null) == (originalSelfVar == null);
	assert paramTerms != null;
	assert paramTerms.size() == originalParamVars.size();
	assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	map.put(TB.heap(TB.BASE_HEAP_NAME, services), heapTerm);
	if (originalSelfVar != null) {
	    map.put(TB.var(originalSelfVar), selfTerm);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(TB.var(originalParamVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}	
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalMby);
    }    
   
    
    @Override
    public String getHTMLText(Services services) {
	final String pre = LogicPrinter.quickPrintTerm(originalPre, services);
        final String mby = hasMby() 
        	           ? LogicPrinter.quickPrintTerm(originalMby, services)
        	           : null;
        final String dep = LogicPrinter.quickPrintTerm(originalDep, services);
                      
        return "<html>"
                + "<b>pre</b> "
                + LogicPrinter.escapeHTML(pre, false)
                + "<br><b>dep</b> "
                + LogicPrinter.escapeHTML(dep, false)
                + (hasMby() 
                   ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby, 
                	   						 false)
                   : "")                
                + "</html>";
    }    
    
    
    @Override
    public boolean toBeSaved() {
	return false; //because dependency contracts currently cannot be
	              //specified directly in DL 
    }
    
    
    @Override
    public String proofToString(Services services) {
	assert false;
	return null;
    }
    

    @Override
    public Term getDep(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	if (originalSelfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(originalParamVar, paramVars.head());
	    paramVars = paramVars.tail();
	}
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalDep);
    }
    

    @Override
    public Term getDep(Term heapTerm,
	               Term selfTerm, 
	               ImmutableList<Term> paramTerms, 
	               Services services) {
	assert heapTerm != null;
	assert (selfTerm == null) == (originalSelfVar == null);
	assert paramTerms != null;
	assert paramTerms.size() == originalParamVars.size();
	assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	map.put(TB.heap(TB.BASE_HEAP_NAME, services), heapTerm);
	if (originalSelfVar != null) {
            map.put(TB.var(originalSelfVar), selfTerm);
        }
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(TB.var(originalParamVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}	
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalDep);
    }    
    
    
    @Override
    public String toString() {
	return originalDep.toString();
    }


    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, kjt, target, id);
    }


    @Override
    public VisibilityModifier getVisibility() {
	return null;
    }

    @Override
    public boolean transactionContract() {
        return false;
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
	    Contract contract) {
	return new DependencyContractPO(initConfig,
	        (DependencyContract) contract);
    }


    @Override
    public DependencyContract setID(int newId) {
        return new DependencyContractImpl(baseName,
                                          null,
                                          kjt,
                                          target,
                                          originalPre,
                                          originalMby,
                                          originalDep,
                                          originalSelfVar,
                                          originalParamVars,
                                          newId);
    }


    @Override
    public Contract setTarget(KeYJavaType newKJT,
                              ObserverFunction newPM) {
        return new DependencyContractImpl(baseName,
                                          null,
                                          newKJT,
                                          newPM,
                                          originalPre,
                                          originalMby,
                                          originalDep,
                                          originalSelfVar,
                                          originalParamVars,
                                          id);
    }
    
    
    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, kjt, target);
    }
}
