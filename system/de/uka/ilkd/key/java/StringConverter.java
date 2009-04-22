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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;




public  class StringConverter{
	
        /** used for the pretty printer*/ 
        /*Function ppCat;
        static final String EPSILON="epsilon";
        static final String CAT="cat";*/

    static final String EMPTY="empty";
    static final String CONS="cons";

    //private final TermBuilder TB = TermBuilder.DF;

        /** translates a given literal to its logic counterpart.
         *  the string has to be enclosed by quotation marks.
         */
        
        public Term translateLiteral(Literal lit, LDT charLDT, Services serv){
	    Namespace funcNs = serv.getNamespaces().functions();
	    Function empty= (Function)funcNs.lookup(new Name(EMPTY));
	    assert empty != null;
	    Function cons=(Function)funcNs.lookup(new Name(CONS));
	    assert cons != null;
	    
	    Term  term_empty=TermFactory.DEFAULT.createFunctionTerm(empty);

	    // TB.func(empty) TB.func(cons, character)

	    char[] charArray;
	    Term result = term_empty;

	    if (lit instanceof StringLiteral)
		charArray = ((StringLiteral) lit).getValue().toCharArray();
	    else
		return null;
	    if (charLDT==null)
		throw new IllegalArgumentException("CharLDT is needed for StringLiteral translation");
	    for (int i= charArray.length-2;i>=1;i--) {
		result = TermFactory.DEFAULT.createFunctionTerm(cons,
		    charLDT.translateLiteral(new CharLiteral(charArray[i])),result);
	    }

	    return result;
	}

    	private StringBuffer printlastfirst(Term t) {
	    if (t.op().arity()==0) {
		return new StringBuffer();
	    } else {
		return printlastfirst(t.sub(0)).append(t.op().name().toString());
	    }
	}

	private String translateCharTerm(Term t)
        {
	    char charVal=0;
	    int intVal=0;
	    String result = printlastfirst(t.sub(0)).toString();
	    try {
		intVal = Integer.parseInt(result);
		charVal = (char)intVal;
		if (intVal-charVal!=0)
		    throw new NumberFormatException(); //overflow!
		
	    } catch (NumberFormatException ex) {
		throw new ConvertException(result +" is not of type char");
	    } 		
	    return new Character(charVal).toString();
	}
     
	/** translates a term that represents a string into a string literal
         *  that is enclosed by quotation marks 
	 */

        public Expression translateTerm(Term  t, ExtList  children){
	    final StringBuffer result = new StringBuffer("");
	    Term term = t;
	    while (term.op().arity()!=0){
		result.append(translateCharTerm(term.sub(0)));
		term = term.sub(1);
	    }
	    return new StringLiteral("\""+result+"\"");
	}

    }
