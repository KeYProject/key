// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;


/** 
 * Abstract operator class offering some common functionality.
 */
abstract class AbstractOperator implements Operator {
    
    private final Name name;
    private final int arity;
    private final ImmutableArray<Boolean> whereToBind;
    private final boolean isRigid;
    
    
    protected AbstractOperator(Name name, 
	    		       int arity, 
	    		       ImmutableArray<Boolean> whereToBind,
	    		       boolean isRigid) {
	assert name != null;
	assert arity >= 0;
	assert whereToBind == null || whereToBind.size() == arity;	
	this.name = name;
	this.arity = arity;
	this.whereToBind = whereToBind;
	this.isRigid = isRigid;
    }
    
    
    protected AbstractOperator(Name name, 
	    		       int arity, 
	    		       Boolean[] whereToBind,
	    		       boolean isRigid) {
	this(name, arity, new ImmutableArray<Boolean>(whereToBind), isRigid);
    }        
    
    
    protected AbstractOperator(Name name, int arity, boolean isRigid) {
	this(name, arity, (ImmutableArray<Boolean>) null, isRigid);
    }
    
    
    protected final ImmutableArray<Boolean> whereToBind() {
	return whereToBind;
    }
    
    
    @Override
    public final Name name() {
	return name;
    }
    
    
    @Override
    public final int arity() {
        return arity;
    }
    
    
    @Override
    public final boolean bindVarsAt(int n) {
	return whereToBind != null && whereToBind.get(n);
    }
    
    
    @Override
    public final boolean isRigid() {
	return isRigid;
    }
    
    
    /**
     * Allows subclasses to impose custom demands on what constitutes a 
     * valid term using the operator represented by the subclass. 
     */
    protected abstract boolean additionalValidTopLevel(Term term);
    
    
    @Override
    public boolean validTopLevel(Term term) {
	if(arity != term.arity()
	   || arity != term.subs().size()
	   || (whereToBind == null) != term.boundVars().isEmpty()) {
	    return false;
	}
	
	for(int i = 0, n = arity; i < n; i++) {
	    if(term.sub(i) == null) {
		return false;
	    }
	}
	
	return additionalValidTopLevel(term);
    }
    
    
    @Override
    public String toString() {
	return name().toString();
    }
}