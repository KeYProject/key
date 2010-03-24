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
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;


/**
 * Because instances of SMTSolvers are stateless all
 * data of this instances is stored in SolverSession.
 */
class SolverSession {
    

    /**
     * This class is used to associated the goal with its term and result.
     * 
     */
    public static class InternResult implements Cloneable {
	private SMTSolverResult result = SMTSolverResult.createUnknownResult("", "");
	private Term            term;
	private Goal 		goal;
	private String 		formula = null;
	
	

	public InternResult(Term term, Goal belongsTo){
	    this(term);
	    goal = belongsTo;
	}
	
	/**
	 * Sometimes there is no goal.
	 * @param term
	 */
	public InternResult(Term term) {
	    super();
	    this.term = term;
        }
	
	InternResult(Term term, Goal goal, String formula){
	    this(term,goal);
	    this.formula = formula;
	}
	
	
	
	public InternResult(String formula){
	    this(null,null);
	    this.formula = formula;
	}
	
	/**
	 * @return the goal associated with the term.
	 */
	public Goal getGoal(){
	    return goal;
	}
	
	/**
	 * @return the term that belongs to that instance.
	 */
	public Term getRealTerm(){
	    return term;
	}
	
	void setResult(SMTSolverResult res){
	    if(result.isValid() == ThreeValuedTruth.UNKNOWN){
		result = res;
	    }
	    
	}
	
	

	
	String getFormula(){
	   return formula; 
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
	
	/* (non-Javadoc)
	 * @see java.lang.Object#clone()
	 */
	@Override
	protected Object clone() throws CloneNotSupportedException {
	    return new InternResult(term , goal ,formula);
	}
	
		

	
	public String toString(){
	    return goal == null ? "" : goal +":" +result;
	}

	
	
    }
     
    private LinkedList<InternResult> terms;
    private Services         services;
    private Iterator<InternResult>   it;
    private InternResult      current = null;
    private Collection<Taclet>    taclets;
    
    public Collection<InternResult> getTerms() {
        return terms;
    }
    public Services getServices() {
        return services;
    }
    
    
    
    public SolverSession(LinkedList<InternResult> terms, Services services, Collection<Taclet> taclets) {
	super();
	this.terms = terms;
	this.services = services;
	this.taclets = taclets;
	it = terms.iterator();
    }
    
    public Collection<Taclet> getTaclets(){
	return taclets;
    }
    
    public InternResult getLastResult(){
	return current;
    }
    
    public InternResult nextTerm(){
	if(it.hasNext()){
	    current = it.next();
	    
	} else {
	    current = null;
	}
	return current;
    }
    
    public InternResult currentTerm(){
	return current;
    }
    
    public boolean hasNextTerm(){
	return it.hasNext();
    }
    

    
    public LinkedList<InternResult> getResults(){
	return terms;
    }
    
    public int getTermSize(){
	return terms.size();
    }

}
