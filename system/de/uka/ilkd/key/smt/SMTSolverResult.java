// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;


public final class SMTSolverResult {
    
    /** In the context of proving nodes/sequents these values mean the following:
     * TRUE means that the negation of the sequent is unsatisfiable,
     * FALSE means that the negation of the sequent is satisfiable (i.e. it has a counterexample),
     * UNKNOWN means, well, unknown
     * Note: Currently (1.12.'09) the SMT Solvers do not check if a node is FALSE. 
     */
    public static enum ThreeValuedTruth {TRUE, FALSE, UNKNOWN}
    
    private final String text;
    private final ThreeValuedTruth isValid;
    private static int idCounter = 0;
    private final int id = ++idCounter;
    
    /**This is to identify where the result comes from. E.g. for user feedback. */
    public final String solverName;
    
    private SMTSolverResult(String text, ThreeValuedTruth isValid, String solverName) {
	this.solverName = solverName;
	this.text = text;
	this.isValid = isValid;
    }
    
    public int getID() {
	return id;
    }
    
    
    public static SMTSolverResult createValid(String text, String solverName) {
	return new SMTSolverResult(text, ThreeValuedTruth.TRUE, solverName);
    }
    
    
    public static SMTSolverResult createInvalid(String text, String solverName) {
	return new SMTSolverResult(text, ThreeValuedTruth.FALSE, solverName);
    }
    
    
    public static SMTSolverResult createUnknown(String text, String solverName) {
	return new SMTSolverResult(text, ThreeValuedTruth.UNKNOWN, solverName);
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
