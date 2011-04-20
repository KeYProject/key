// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;


public abstract class KeYExceptionHandlerImpl implements KeYExceptionHandler {

    protected ExtList exceptions = null; 

    public KeYExceptionHandlerImpl() {
	exceptions = new ExtList();
    }

    
    @Override
    public void reportException(Throwable e) {
	exceptions.add(e);
    }

    
    @Override    
    public ExtList getExceptions() {
	return exceptions;
    }

        
    @Override    
    public void clear() {
	exceptions = new ExtList();	
    }
}
