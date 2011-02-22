package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;


public class SMTProblem{
    private Term term;
    private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();
    private Object userTag;
    private String name = "";
    public Term getTerm() {
	return term;
    }
    void addSolver(SMTSolver solver){
	solvers.add(solver);
    }
    
    public Collection<SMTSolver> getSolvers() {
	return solvers;
    }
    
    public SMTProblem(Goal goal,Object userTag){
	name = "Goal "+goal.node().serialNr();
	term = goalToTerm(goal);
	this.userTag = userTag;
    }
    
    public Object getUserTag(){
	return userTag;
    }
    
    
    public String getName(){
	return name;
    }
    
    
    
    private Term goalToTerm(Goal goal){
	Sequent s = goal.sequent();
	
	ImmutableList<Term> ante = ImmutableSLList.nil();
	
	ante = ante.append(TermBuilder.DF.tt());
	for(ConstrainedFormula f : s.antecedent()){
	    ante = ante.append(f.formula());
	}
	
	ImmutableList<Term> succ = ImmutableSLList.nil();
	succ = succ.append(TermBuilder.DF.ff());
	for(ConstrainedFormula f : s.succedent()){
	    succ = succ.append(f.formula());
	}
	
	
	return TermBuilder.DF.imp(TermBuilder.DF.and(ante), TermBuilder.DF.or(succ));
	
    }
    
    public static Collection<SMTProblem> createSMTProblems(Proof proof){
	LinkedList<SMTProblem> problems = new LinkedList<SMTProblem>();
	for(Goal goal : proof.openGoals()){
	    problems.add(new SMTProblem(goal,goal));
	}
	return problems;
    }
}