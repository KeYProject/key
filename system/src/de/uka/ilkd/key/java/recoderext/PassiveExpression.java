// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.expression.ParenthesizedExpression;


public class PassiveExpression
    extends ParenthesizedExpression {

        
    /**
     * 
     */
    private static final long serialVersionUID = 4916068787633267648L;

    /**
     * creates a newly generated passive expression
     */
    public PassiveExpression() {
	super();
    }

    /**
     * creates a newly generated passive expression
     */
    public PassiveExpression(Expression e) {
	super(e);
    }

    public PassiveExpression(PassiveExpression proto) {
	super(proto);
    }
	   
    public PassiveExpression deepClone() {
	return new PassiveExpression(this);
    }
}
