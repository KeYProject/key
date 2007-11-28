// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser.jml;

public class NotSupportedExpressionException extends antlr.RecognitionException{

    private boolean canBeIgnored = false;
    private String expression = "";

    public NotSupportedExpressionException(String s){
	super("This feature is not yet supported: "+s);
	expression = s;
    }

    public NotSupportedExpressionException(String s, boolean canBeIgnored){
	super("This feature is not yet supported: "+s);
	this.canBeIgnored = canBeIgnored;
	expression = s;
    }

    /**
     * True if ignoring the unsupported expression doesn't change the semantics
     * of the affected specification. 
     */
    public boolean canBeIgnored(){
	return canBeIgnored;
    }

    public String expression(){
	return expression;
    }

}
