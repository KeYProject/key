// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                          Universitaet Koblenz-Landau, Germany
//                          Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.ldt;

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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ConvertException;

/**
 * This class inherits from LDT and implements methods to translate
 * String Literals into its logic counterpart, i.e. a CharList term.
 */
public class StringLDT extends LDT {

    public static final Name POOL_NAME = new Name("pool");

    public static final Name CONTENT_NAME = new Name("content");

    public static final Name CONS = new Name("cons");
    
    public static final Name EMPTY = new Name("empty");

    public static final Name CHAR_AT = new Name("charAt");

    public static final Name INDEX_OF = new Name("indexOf");

    public static final Name LAST_INDEX_OF = new Name("lastIndexOf");

    
    /** the CharLDT used for translation of StringLiterals */
    CharLDT charLDT;

    /** the functions building up a term */
    Function cons;
    Function empty;

    public StringLDT(Services services, Namespace sorts, Namespace functions, CharLDT charLDT) {
	super(new Name("java.lang.String"), sorts, null);
	// instead of null should be: services.getJavaInfo().getTypeByName("java.lang.String").getJavaType();
	// but getTypeName yields null!
	this.charLDT = charLDT;
	cons  = addFunction (functions, CONS.toString());
	empty = addFunction (functions, EMPTY.toString());
    }

    /**
     * returns true if the LDT is responsible for this kind of literals
     * 
     * @param lit
     *            the Literal
     * @return true if the LDT is responsible for this kind of literals
     */
    public boolean isResponsible(Literal lit) {
	return lit instanceof StringLiteral;
    }

    /**
     * returns true if the LDT offers an operation for the given java operator
     * and the logic subterms
     * 
     * @param op
     *            the de.uka.ilkd.key.java.expression.Operator to translate
     * @param subs
     *            the logic subterms of the java operator
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterms
     */
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    Term[] subs, Services services, ExecutionContext ec) {
	return false;
    }

    /**
     * returns true if the LDT offers an operation for the given binary java
     * operator and the logic subterms
     * 
     * @param op
     *            the de.uka.ilkd.key.java.expression.Operator to translate
     * @param left
     *            the left subterm of the java operator
     * @param right
     *            the right subterm of the java operator
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterms
     */
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    Term left, Term right, Services services, ExecutionContext ec) {
	return false;
    }

    /**
     * returns true if the LDT offers an operation for the given unary java
     * operator and the logic subterms
     * 
     * @param op
     *            the de.uka.ilkd.key.java.expression.Operator to translate
     * @param sub
     *            the logic subterms of the java operator
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterm
     */
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    Term sub, Services services, ExecutionContext ec) {
	return false;
    }

     /**
     * translates a given literal to its logic counterpart
     * 
     * @param lit
     *            the Literal to be translated
     * @return the Term that represents the given literal in its logic form
     */
    public Term translateLiteral(Literal lit) {
	assert empty != null && cons != null;
	
	Term  term_empty=TermFactory.DEFAULT.createFunctionTerm(empty);
	// TB.func(empty) TB.func(cons, character)
	
	char[] charArray;
	Term result = term_empty;
	
	if (lit instanceof StringLiteral)
	    charArray = ((StringLiteral) lit).getValue().toCharArray();
	else
	    return null;

	for (int i= charArray.length-2;i>=1;i--) {
	    result = TermFactory.DEFAULT.createFunctionTerm(cons,
							    charLDT.translateLiteral(new CharLiteral(charArray[i])),result);
	}

	return result;
    }

    /**
     * returns the function symbol for the given operation
     * 
     * @return the function symbol for the given operation
     */
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
	    Services services, ExecutionContext ec) {
	return null;
    }

    public boolean hasLiteralFunction(Function f) {
	return false;
    }

    private StringBuffer printlastfirst(Term t) {
	if (t.op().arity()==0) {
	    return new StringBuffer();
	} else {
	    return printlastfirst(t.sub(0)).append(t.op().name().toString());
	}
    }

    private String translateCharTerm(Term t) {
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
    public Expression translateTerm(Term t, ExtList children) {
	final StringBuffer result = new StringBuffer("");
	Term term = t;
	while (term.op().arity()!=0){
	    result.append(translateCharTerm(term.sub(0)));
	    term = term.sub(1);
	}
	return new StringLiteral("\""+result+"\"");
    }

}