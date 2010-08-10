// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;

import de.uka.ilkd.key.proof.init.ProofInputException;

public class KeYExceptionHandlerImpl implements KeYExceptionHandler{

    protected ExtList exceptions = null; 

    public KeYExceptionHandlerImpl(){
	exceptions = new ExtList();
    }

    public void reportException(Throwable e){
        if (e != ProofInputException.USER_ABORT_EXCEPTION) {
            exceptions.add(e);
        } else {
            // HACK avoids annoying error dialog after the user
            // cancelled loading of a proof with the JMLSpecBrowser 
        }
    }

    public ExtList getExceptions(){
	return exceptions;
    }

    /** errors? 
     * @return boolean true if errors or exceptions were reported, 
     * false otherwise
     */
    public boolean error() {
	return !exceptions.isEmpty();
    }

    public void clear(){
	exceptions = new ExtList();	
    }

}
