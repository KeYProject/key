// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.unittest.simplify.translation;

/**
 * This class is just a return value
 */
public class DecisionProcedureResult {

    private String text;

    private boolean result;

    private SimplifyTranslation translation;

    public DecisionProcedureResult(boolean b, String s) {
	this(b, s, null);
    }

    public DecisionProcedureResult(boolean b, String s, SimplifyTranslation tr) {
	text = s;
	result = b;
	translation = tr;
    }


    public boolean getResult() {
	return result;
    }

    public String getText() {
	return text;
    }

    public SimplifyTranslation getTranslation() {
	return translation;
    }

}
