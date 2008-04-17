// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.util;


/** This Exception is only thrown by the ExceptionHandler */

public class ExceptionHandlerException extends RuntimeException{

    public ExceptionHandlerException(){
	super("An Exception occurred");
    }

    public ExceptionHandlerException(String msg){
	super(msg);
    }

    public ExceptionHandlerException(Throwable ex){
	super(ex);
    }

}
