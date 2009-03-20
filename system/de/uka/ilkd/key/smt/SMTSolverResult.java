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
    
    public static enum ThreeValuedTruth {TRUE, FALSE, UNKNOWN}
    
    public static final SMTSolverResult NO_IDEA 
    	= new SMTSolverResult("", ThreeValuedTruth.UNKNOWN);
    
    
    private final String text;
    private final ThreeValuedTruth isValid;
    
    
    private SMTSolverResult(String text, ThreeValuedTruth isValid) {
	this.text = text;
	this.isValid = isValid;
    }
    
    
    public static SMTSolverResult createValidResult(String text) {
	return new SMTSolverResult(text, ThreeValuedTruth.TRUE);
    }
    
    
    public static SMTSolverResult createInvalidResult(String text) {
	return new SMTSolverResult(text, ThreeValuedTruth.FALSE);
    }
    
    
    public static SMTSolverResult createUnknownResult(String text) {
	return new SMTSolverResult(text, ThreeValuedTruth.UNKNOWN);
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
