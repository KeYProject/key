// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;


public final class DependencyContractImpl implements Contract {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final String baseName;    
    private final String name;
    private final KeYJavaType kjt;
    private final ObserverFunction target;
    private final Term originalDep;
    private final ProgramVariable originalSelfVar;
    private final ImmutableList<ProgramVariable> originalParamVars;
    private final int id;    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private DependencyContractImpl(String baseName,
	                           String name, 
	                           KeYJavaType kjt,
	    			   ObserverFunction target,
	                  	   Term dep,
	                  	   ProgramVariable selfVar,
	                  	   ImmutableList<ProgramVariable> paramVars,
	                  	   int id) {
	assert baseName != null;
	assert kjt != null;
	assert target != null;
	assert dep != null;
        assert (selfVar == null) == target.isStatic();
        assert paramVars != null;
        assert paramVars.size() == target.arity() - (target.isStatic() ? 1 : 2);
	this.baseName = baseName;
        this.name                   = name != null 
                                      ? name 
                                      : baseName + " [id: " + id + " / " 
                                        + target
                                        + " for " 
                                        + kjt.getJavaType().getName() 
                                        + "]";
	this.kjt = kjt;
	this.target = target;
	this.originalDep = dep;
	this.originalSelfVar = selfVar;
	this.originalParamVars = paramVars;
	this.id = id;
    }
    
    
    public DependencyContractImpl(String baseName, 
	                          KeYJavaType kjt,
	    			  ObserverFunction target,
	                  	  Term dep,
	                  	  ProgramVariable selfVar,
	                  	  ImmutableList<ProgramVariable> paramVars) {
	this(baseName, null, kjt, target, dep, selfVar, paramVars, INVALID_ID);
    }    
    
    
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
    public Contract setID(int newId) {
        return new DependencyContractImpl(baseName,
        	                          null,
                			  kjt,        	                         
                			  target,
                			  originalDep,
                			  originalSelfVar,
                			  originalParamVars,
                			  newId);	
    }
    
    
    @Override
    public Contract setTarget(KeYJavaType newKJT,
	    		      ObserverFunction newTarget, 
	    		      Services services) {
        return new DependencyContractImpl(baseName,
        				  null,
                			  newKJT,        				 
                			  newTarget,
                			  originalDep,
                			  originalSelfVar,
                			  originalParamVars,
                			  id);	
    }    
    
    
    @Override
    public boolean hasDep() {
	return true;
    }
    
    
    @Override
    public Term getPre(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
	    	       Services services) {
	return TB.tt();
    }
    
    
    @Override
    public Term getPre(Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
	    	       Services services) {
	return TB.tt();
    }    
    
    
    @Override
    public Term getDep(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map map = new HashMap();
	map.put(originalSelfVar, selfVar);
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
	Map map = new HashMap();
	map.put(TB.heap(services), heapTerm);
	map.put(TB.var(originalSelfVar), selfTerm);
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(TB.var(originalParamVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}	
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalDep);
    }
    
    
    @Override
    public String getHTMLText(Services services) {
        final String dep = LogicPrinter.quickPrintTerm(originalDep, services);
                      
        return "<html>"
                + "<b>dep</b> "
                + LogicPrinter.escapeHTML(dep)
                + "</html>";
    }    
    
    
    @Override
    public String toString() {
	return originalDep.toString();
    }
}
