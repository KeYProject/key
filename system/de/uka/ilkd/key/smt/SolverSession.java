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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem.SelectionMode;


class SolverSession {
    

    
    public static class InternResult{
	SMTSolverResult result;
	Term            term;
	Goal 		goal;
	public InternResult(SMTSolverResult result, Term term) {
	    super();
	    this.result = result;
	    this.term = term;
        }
	
	public Goal getGoal(){
	    return goal;
	}
	
	public Term getRealTerm(){
	    return term;
	}
	
	public InternResult(Term term, Goal belongingTo){
	    this(SMTSolverResult.createUnknownResult("", ""),term);
	    goal = belongingTo;
	}
	
	
		@Override
	public int hashCode() {
	    if(goal != null)
	    return goal.hashCode();
	    else return super.hashCode();
	}
		
	public SMTSolverResult getResult(){
	    return result;
	}
	
		
	@Override
	public boolean equals(Object obj) {
	    if(!(obj instanceof InternResult)){
		return false;
	    }
	    InternResult r = ((InternResult)obj);
	    if(goal == null || r.goal == null){
		return false;
	    }
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
	
	public String toString(){
	    return goal == null ? "" : goal +":" +result;
	}
	
    }
     
    private LinkedList<InternResult> terms;
    //private LinkedList<InternResult> results = new LinkedList<InternResult>();
    private Services         services;
    private Iterator<InternResult>   it;
    private InternResult      current = null;
    private TacletIndex      tacletIndex;
    
    public Collection<InternResult> getTerms() {
        return terms;
    }
    public Services getServices() {
        return services;
    }
    
    
    
    public SolverSession(LinkedList<InternResult> terms, Services services, TacletIndex index) {
	super();
	this.terms = terms;
	this.services = services;
	tacletIndex = index;
	it = terms.iterator();
    }
    
    public TacletIndex getTacletIndex(){
	return tacletIndex;
    }
    
    public InternResult getLastResult(){
	return current;
    }
    
    public InternResult nextTerm(){
	if(it.hasNext()){
	    current = it.next();
	    return current;
	}
	return null;
    }
    
    public InternResult currentTerm(){
	return current;
    }
    
    public boolean hasNextTerm(){
	return it.hasNext();
    }
    
    /*public void addResult(SMTSolverResult result, Term term){
	results.add(new InternResult(result,term));
    }*/
    
    public LinkedList<InternResult> getResults(){
	return terms;
    }
    
    public int getTermSize(){
	return terms.size();
    }

}
