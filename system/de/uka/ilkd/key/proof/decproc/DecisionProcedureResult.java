// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.decproc;

import de.uka.ilkd.key.logic.Constraint;

/** This class is just a return value
 */
public class DecisionProcedureResult {
    protected String text;
    protected boolean result;
    protected String notes;
    protected Constraint constraint = Constraint.BOTTOM;
    protected DecProcTranslation translation;

    public String getText() {
	return text;
    }

    public String getNotes() {
	return notes;
    }

    public Constraint getConstraint() {
	return constraint;
    }    

    public boolean getResult() {
	return result;
    }

    public DecProcTranslation getTranslation(){
	return translation;
    }

    public DecisionProcedureResult(boolean b, String s, Constraint c) {
	this(b, s, c, null);
    }

    public DecisionProcedureResult(boolean b, String s, Constraint c, 
				   DecProcTranslation tr) {
	text = s;
	result = b;
	constraint = c;	
	translation = tr;
    }

}
