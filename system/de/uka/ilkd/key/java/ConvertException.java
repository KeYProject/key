// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

/**
 * This exception class is mainly thrown by Recoder2KeY and its companions.
 * 
 * It stores its reason not only by the cause mechanism of Exceptions but also
 * separately if it is a parser error.
 * 
 * This information is then read by the KeYParser to produce helpful error
 * messages.
 * 
 */
public class ConvertException extends RuntimeException {

	public ConvertException(String errmsg) {
		super(errmsg);
	}

	public ConvertException(Throwable pe) {
        super(pe);
	}

	public ConvertException(String errmsg, Throwable cause) {
		super(errmsg, cause);
	}
    
	public recoder.parser.ParseException parseException() {
		if (getCause() instanceof recoder.parser.ParseException) {
			return (recoder.parser.ParseException) getCause();
		} else {
			return null;
		}
	}

	public de.uka.ilkd.key.parser.proofjava.ParseException proofJavaException() {
		if (getCause() instanceof de.uka.ilkd.key.parser.proofjava.ParseException) {
			return (de.uka.ilkd.key.parser.proofjava.ParseException) getCause();
		} else {
			return null;
		}
	}

	public String getMessage() {
		String mess = super.getMessage();
		if (getCause() != null && getCause().getMessage() != null) {
			return mess + " - " + getCause().getMessage();
		}
		return mess;
	}
    
}
