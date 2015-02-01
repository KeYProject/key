// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;


/** This Exception is only thrown by the ExceptionHandler */

public class ExceptionHandlerException extends RuntimeException {

    /**
     * 
     */
    private static final long serialVersionUID = 4804191909840321109L;

    public ExceptionHandlerException() {
	super("An Exception occurred");
    }

    public ExceptionHandlerException(String msg) {
	super(msg);
    }

    public ExceptionHandlerException(Throwable ex) {
	super(ex);
    }
    
    @Override
    public String getMessage() {
    	return toString();
    }

    @Override
    public String toString() {
    	return super.getMessage();
    }
}