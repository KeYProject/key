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
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.proof.OpReplacer;


public final class DependencyContractImpl implements DependencyContract {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final String name;
    private final KeYJavaType kjt;
    private final Operator observer;
    private final Term originalDependencies;
    private final ParsableVariable originalSelfVar;
//    private final ImmutableList<ParsableVariable> originalParamVars;
    
    public DependencyContractImpl(String name, 
	                          KeYJavaType kjt,
	    			  Operator observer,
	                  	  Term dependencies,
	                  	  ParsableVariable selfVar) {
	this.name = name;
	this.kjt = kjt;
	this.observer = observer;
	this.originalDependencies = dependencies;
	this.originalSelfVar = selfVar;
    }
    

    @Override
    public String getName() {
	return name;
    }
    

    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }

    
    @Override
    public Operator getObserver() {
	return observer;
    }
    

    @Override
    public Term getDependencies(ParsableVariable selfVar,
	                        Services services) {	
	Map map = new HashMap();
	map.put(originalSelfVar, selfVar);
	OpReplacer or = new OpReplacer(map);
	Term dependencies = or.replace(originalDependencies);
	return dependencies;
    }
    
    
    
    @Override
    public String toString() {
	return originalDependencies.toString();
    }
}
