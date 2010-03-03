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
import de.uka.ilkd.key.smt.taclettranslation.TreeItem.SelectionMode;


class SolverSession {
    
    public class InternResult{
	SMTSolverResult result;
	Goal            goal;
	public InternResult(SMTSolverResult result, Goal goal) {
	    super();
	    this.result = result;
	    this.goal = goal;
        }
	
		@Override
	public int hashCode() {
	   
	    return goal.hashCode();
	}
		
	@Override
	public boolean equals(Object obj) {
	    if(!(obj instanceof InternResult)){
		return false;
	    }
	    InternResult r = ((InternResult)obj);
	    
	    if(goal.equals(r.goal)){
		if(r.result.isValid() == result.isValid()){
		    return true;
		}
		if((r.result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE &&
			result.isValid() == SMTSolverResult.ThreeValuedTruth.UNKNOWN) ||
			(r.result.isValid() == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE &&
				result.isValid() == SMTSolverResult.ThreeValuedTruth.UNKNOWN))
		{
		    result = r.result;
		}

		if(result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE &&
			r.result.isValid() == SMTSolverResult.ThreeValuedTruth.UNKNOWN ||
			(result.isValid() == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE &&
				r.result.isValid() == SMTSolverResult.ThreeValuedTruth.UNKNOWN))
		{
		    r.result = result;
		}

		return true;
	    }

	    return false;

	}
	
    }
     
    private Collection<Goal> goals;
    private LinkedList<InternResult> results = new LinkedList<InternResult>();
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
    
    public void addResult(SMTSolverResult result, Goal goal){
	results.add(new InternResult(result,goal));
    }
    
    public LinkedList<InternResult> getResults(){
	return results;
    }
    
    public int getGoalSize(){
	return goals.size();
    }

}
