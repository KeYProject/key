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
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
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
        Function ppCat;
        static final String EPSILON="epsilon";
        static final String CAT="cat";

        /** translates a given literal to its logic counterpart.
         *  the string has to be enclosed by quotation marks.
         */
        
        public Term translateLiteral(Literal lit, LDT intLDT, Services serv){
	    Namespace funcNs = serv.getNamespaces().functions();
	    Function epsilon= (Function)funcNs.lookup(new Name(EPSILON));
	    Function cat=(Function)funcNs.lookup(new Name(CAT));
	    if(epsilon==null || cat==null){
		throw new RuntimeException("Functions namespace does not know the string-related functions: "+EPSILON+" and "+CAT+". Try to enable Menu > Options > TacletLibraries > stringRules.key ");
	    }
	    assert epsilon != null;
	    assert cat != null;
	    ppCat = cat;
	    Term  term_epsilon=TermFactory.DEFAULT.createFunctionTerm(epsilon);

	    char[] charArray;
	    Term result = term_epsilon;

	    if (lit instanceof StringLiteral)
		charArray = ((StringLiteral) lit).getValue().toCharArray();
	    else return null;
	    if (intLDT==null) throw new IllegalArgumentException("IntLDT is needed for StringLiteral translation");//return term_epsilon;
	    for (int i= charArray.length-2;i>=1;i--){
		result = TermFactory.DEFAULT.createFunctionTerm(cat,
		    intLDT.translateLiteral(new IntLiteral(charArray[i])),result);
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

        /** @return the function symbol that is used to build strings*/         
	public  Function  getStringSymbol(){
	    return ppCat;
	}
	
    }
