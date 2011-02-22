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
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;


public class SMTProblem{
    private Term term;
    private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();
    private Goal goal;
    private Sequent sequent;
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
    
    public SMTProblem(Goal goal){
	name = "Goal "+goal.node().serialNr();
	term = goalToTerm(goal);
	this.goal = goal;
    }
    
    public SMTProblem(Sequent sequent){
	term = sequentToTerm(sequent);
	this.sequent = sequent;
	
    }
    
    public Goal getGoal() {
	return goal;
    }
    
    public Sequent getSequent() {
	return sequent;
    }
    
    public SMTSolverResult getFinalResult(){
	SMTSolverResult unknown = SMTSolverResult.NO_IDEA;
	SMTSolverResult valid = null;
	SMTSolverResult invalid = null;
	for(SMTSolver solver : solvers){
	    if(solver.getFinalResult().isValid() == ThreeValuedTruth.TRUE){
		valid =  solver.getFinalResult();
	    }else if(solver.getFinalResult().isValid() == ThreeValuedTruth.FALSIFIABLE){
		valid =  solver.getFinalResult();
	    }else{
	        unknown = solver.getFinalResult();
	    }
	}
	if(valid != null && invalid != null){
	    throw new RuntimeException("FATAL ERROR: The results are inconsistent!");
	}
	if(valid != null){
	    return valid;
	}
	if(invalid != null){
	    return invalid;
	}
	return unknown;
    }

    
    public String getName(){
	return name;
    }
    
    private Term sequentToTerm(Sequent s){
	
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
    
    private Term goalToTerm(Goal g){
	sequent = g.sequent();
	return sequentToTerm(sequent);
    }
    
    public static Collection<SMTProblem> createSMTProblems(Proof proof){
	LinkedList<SMTProblem> problems = new LinkedList<SMTProblem>();
	for(Goal goal : proof.openGoals()){
	    problems.add(new SMTProblem(goal));
	}
	return problems;
    }
}