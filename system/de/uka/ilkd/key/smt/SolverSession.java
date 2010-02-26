// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;



class SolverSession {
    private Collection<Goal> goals;
    private LinkedList<SMTSolverResult> results = new LinkedList<SMTSolverResult>();
    private Services         services;
    private Iterator<Goal>   it;
    private Goal	      current = null;
    
    public Collection<Goal> getGoals() {
        return goals;
    }
    public Services getServices() {
        return services;
    }
    
    public SolverSession(Collection<Goal> goals, Services services) {
	super();
	this.goals = goals;
	this.services = services;
	it = goals.iterator();
    }
    
    public Goal nextGoal(){
	if(it.hasNext()){
	    current = it.next();
	    return current;
	}
	return null;
    }
    
    public Goal currentGoal(){
	return current;
    }
    
    public boolean hasNextGoal(){
	return it.hasNext();
    }
    
    public void addResult(SMTSolverResult result){
	results.add(result);
    }
    
    public LinkedList<SMTSolverResult> getResults(){
	return results;
    }

}
