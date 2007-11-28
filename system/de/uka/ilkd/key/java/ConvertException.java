// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

public class ConvertException extends RuntimeException {
    
    recoder.parser.ParseException pe=null;
    
    de.uka.ilkd.key.parser.proofjava.ParseException pje;

    public ConvertException(String errmsg) {
	super(""+errmsg);
    }
    
    public ConvertException(recoder.parser.ParseException pe) {
	this.pe=pe;
    }

    public ConvertException(de.uka.ilkd.key.parser.proofjava.ParseException pe){
	this.pje = pe;
    }

    public recoder.parser.ParseException parseException() {
	return pe;
    }

    public de.uka.ilkd.key.parser.proofjava.ParseException proofJavaException(){
	return pje;
    }

    public String getMessage() {
	if (pe!=null) return pe.getMessage();
	if (pje!=null) return pje.getMessage();
	return super.getMessage();
    }

}
