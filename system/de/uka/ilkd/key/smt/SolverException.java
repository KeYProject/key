package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.LinkedList;

/**
 * Encapsulates all exceptions that have occurred while
 * executing the solvers.
 * */
public class SolverException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();

    public SolverException(Collection<SMTSolver> solvers) {
	super();
	this.solvers = solvers;
    }
    public Collection<SMTSolver> getSolvers() {
	return solvers;
    }
    
    @Override
    public void printStackTrace() {
	System.err.println(toString());
    }
    
    public String toString(){
	String s = "\n";
	for(SMTSolver solver : solvers){
	    s += "Solver: " + solver.name()+"\n";
	    if(solver.getProblem().getGoal()!=null){
		s += "Goal-No.: " + solver.getProblem().getGoal().node().serialNr()+"\n";
	    }
	    s += "Exception:\n";
	    s += solver.getException();
	    s += "\n";
	   
	}
	return s;
    }
}
