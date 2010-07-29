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


import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.logic.ldt.StringLDT;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.TermSymbol;




public  class StringConverter {

    static final String EMPTY="empty";
    static final String CONS="cons";
        
    /**
     * translates a given literal to its logic counterpart
     * 
     * @param lit
     *            the Literal to be translated
     * @return the Term that represents the given literal in its logic form
     */
    public Term translateLiteral(Literal lit, LDT charLDT, Services serv) {
	Namespace funcNs = serv.getNamespaces().functions();
	Function empty= (Function)funcNs.lookup(new Name(EMPTY));
	assert empty != null;
	Function cons=(Function)funcNs.lookup(new Name(CONS));
	assert cons != null;
	
	Term  term_empty=TermFactory.DEFAULT.createFunctionTerm(empty);
	
	char[] charArray;
	Term result = term_empty;
	
	if (lit instanceof StringLiteral)
	    charArray = ((StringLiteral) lit).getValue().toCharArray();
	else
	    return null;
	
	
	if (charLDT==null)
	    throw new IllegalArgumentException("CharLDT is needed for StringLiteral translation");
	
	for (int i = charArray.length-2; i>=1; i--) {
	    result = TermFactory.DEFAULT.createFunctionTerm(cons,
							    charLDT.translateLiteral(new CharLiteral(charArray[i])),result);
	}
	
	result = TermBuilder.DF.func((TermSymbol) serv.getNamespaces().functions().lookup(StringLDT.POOL_NAME), result);


	return result;
    }

}
