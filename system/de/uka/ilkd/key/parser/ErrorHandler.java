// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser;


/** This class is used to collect errors and warnings that occured during parsing */

import java.util.Iterator;
import java.util.Stack;

public class ErrorHandler {

    /** Stack collecting errors and warnings*/
    private Stack errorStack = new Stack();
    
    /** amount of errors */
    private int errors=0;

    /** amount of warnings */
    private int warnings=0;

    /** maximal allowed amount of errors */
    private final int maxErrors=5;

    /** create new errorhandler */
    public ErrorHandler() {
	
    }
    
    /** collect error 
     * @param ex the Exception thrown by the de.uka.ilkd.prins.parser
     */
    public void reportError(Exception ex) {
	if (errors<maxErrors) { // more errors occured than allowed	
	    errors++;
	    errorStack.push(ex);
	}
    }

    /** collect warning 
     * @param ex the Exception thrown by the de.uka.ilkd.prins.parser
     */
    public void reportWarning(Exception ex) {
	warnings++;
        errorStack.push(ex);
    }

    /** errors? 
     * @return boolean true if errors were thrown, false otherwise
     */
    public boolean error() {
	return (errors>0);
    }

    /**warnings? 
     * @return boolean true if warnings were thrown, false otherwise
     */
    public boolean warning() {
	return (warnings>0);
    }

    /** print all collected warnings and errors */
    public void printErrorsAndWarnings() {
	
	// print
        for (Object anErrorStack : errorStack) {
            Exception ex = (Exception) anErrorStack;
            if (ex instanceof WarningException) {
                System.out.println("Warning: " + ex.getMessage());
            } else
                System.out.println("Error: " + ex.getMessage());
        }
	
    }

}
