//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;


public class SMTSolverResult {
    
    /** In the context of proving nodes/sequents these values mean the following:
     * TRUE iff negation of the sequent is unsatisfiable,
     * FALSIFIABLE iff negation of the sequent is satisfiable (i.e. it has a counterexample),
     * UNKNOWN otherwise (I'm not sure if this holds if an error occurs)
     * Note: Currently (1.12.'09) the SMT Solvers do not check if a node is FALSE. */
    public static enum ThreeValuedTruth {TRUE, FALSIFIABLE, UNKNOWN}
    
    //We should get rid of this constant because it does not track the source (the solver) of the result.
    public static final SMTSolverResult NO_IDEA 
    	= new SMTSolverResult("", ThreeValuedTruth.UNKNOWN, "?");
    
    
    private final String text;
    private final ThreeValuedTruth isValid;
    
    /**This is to identify where the result comes from. E.g. for user feedback. */
    public final String solverName;
    
    private SMTSolverResult(String text, ThreeValuedTruth isValid, String solverName) {
	this.solverName = solverName;
	this.text = text;
	this.isValid = isValid;
    }
    
    
    public static SMTSolverResult createValidResult(String text, String name) {
	return new SMTSolverResult(text, ThreeValuedTruth.TRUE, name);
    }
    
    
    public static SMTSolverResult createInvalidResult(String text, String name) {
	return new SMTSolverResult(text, ThreeValuedTruth.FALSIFIABLE, name);
    }
    
    
    public static SMTSolverResult createUnknownResult(String text, String name) {
	return new SMTSolverResult(text, ThreeValuedTruth.UNKNOWN, name);
    }
    
    
    public String text() {
	return text;
    }
    
    
    public ThreeValuedTruth isValid() {
	return isValid;
    }
    
    
    public String toString() {
	return isValid + " (" + text + ")";
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof SMTSolverResult)) {
            return false;
        }
        SMTSolverResult ssr = (SMTSolverResult) o;
        return text.equals(ssr.text) && isValid == ssr.isValid;
    }
    
    
    public int hashCode() {
        return text.hashCode() + isValid.hashCode();
    }

}
