// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//



package de.uka.ilkd.key.counterexample;

public class Clauses {
    private Clause clause;
    private Clauses next;

    public Clauses(){
	clause = null;
        next = null;
    }

    public Clauses(Clause c){
        clause = c;
        next = null;
    }


    public void add(Clause clause){
	this.add(new Clauses(clause));
    }


    public void add(Clauses cs){
	if (clause!=null){
	    Clauses step = this;
	    while(step.next!=null){
		step = step.next;
	    }
	    step.next = cs;
        }
        else {
	    this.clause = cs.getHead();
        }
    }

    public String toString(){
	Clauses step = this;
        String s = step.getClause();
        while(step.next!=null){
	    step = step.next;
            s = s + step.getClause();
        }
	return s;
    }
    
    public String getClause(){
        return clause.toString();
    }
    

    public Clause getHead(){
	return this.clause;
    }
	
    public void addComment(String comment){
	this.add(new Clause("","",comment));
    }

}
