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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;

public class StringConverter {

    public static final Name POOL_NAME = new Name("pool");

    public static final Name CONTENT_NAME = new Name("content");

    public static final Name CONS = new Name("cons");

    public static final Name EMPTY = new Name("empty");

    public static final Name CHAR_AT = new Name("charAt");

    public static final Name INDEX_OF = new Name("indexOf");

    public static final Name LAST_INDEX_OF = new Name("lastIndexOf");

    private final Services services;
    
    public StringConverter(Services s) {
	this.services = s;
    }

    /**
     * translates a given literal to its logic counterpart
     * 
     * @param lit
     *            the Literal to be translated
     * @return the Term that represents the given literal in its logic form
     */
    public Term translateLiteral(Literal lit, LDT charLDT, Services serv) {

	final Namespace funcNs = serv.getNamespaces().functions();

	final Function empty = (Function) funcNs.lookup(EMPTY);
	assert empty != null;

	final Function cons = (Function) funcNs.lookup(CONS);
	assert cons != null;

	final Term term_empty = TermBuilder.DF.func(empty);

	char[] charArray;
	Term result = term_empty;

	if (lit instanceof StringLiteral)
	    charArray = ((StringLiteral) lit).getValue().toCharArray();
	else
	    return null;

	if (charLDT == null)
	    throw new IllegalArgumentException(
		    "CharLDT is needed for StringLiteral translation");

	for (int i = charArray.length - 2; i >= 1; i--) {
	    result = TermFactory.DEFAULT.createFunctionTerm(cons,
		    charLDT.translateLiteral(new CharLiteral(charArray[i])),
		    result);
	}

	return result;
    }

    /**
     * translates a term that represents a string into a string literal that is
     * enclosed by quotation marks
     */
    public Expression translateTerm(Term t, ExtList children) {
	final StringBuffer result = new StringBuffer("");
	Term term = t;
	while (term.op().arity() != 0) {
	    result.append(translateCharTerm(term.sub(0)));
	    term = term.sub(1);
	}
	return new StringLiteral("\"" + result + "\"");
    }

    private String translateCharTerm(Term t) {
	char charVal = 0;
	int intVal = 0;
	String result = printlastfirst(t.sub(0)).toString();
	try {
	    intVal = Integer.parseInt(result);
	    charVal = (char) intVal;
	    if (intVal - charVal != 0)
		throw new NumberFormatException(); // overflow!

	} catch (NumberFormatException ex) {
	    throw new ConvertException(result + " is not of type char");
	}
	return new Character(charVal).toString();
    }

    private StringBuffer printlastfirst(Term t) {
	if (t.op().arity() == 0) {
	    return new StringBuffer();
	} else {
	    return printlastfirst(t.sub(0)).append(t.op().name().toString());
	}
    }

    public Function pool() {	 	
	final Function pool = (Function) services.getNamespaces().functions().lookup(POOL_NAME);
	assert pool != null;
	return pool;
    }

    public Function content() {
	final Function content = (Function) services.getNamespaces().functions().lookup(CONTENT_NAME);
	assert content != null;
	return content;
    }

    public Function empty() {
	final Function empty = (Function) services.getNamespaces().functions().lookup(EMPTY);
	assert empty != null;
	return empty;
    }

    public Function cons() {
	final Function cons = (Function) services.getNamespaces().functions().lookup(CONS);
	assert cons != null;
	return cons;
    }

    public Function charAt() {
	final Function charAt = (Function) services.getNamespaces().functions().lookup(CHAR_AT);
	assert charAt != null;
	return charAt;
    }

    public Function indexOf() {
	final Function indexOf = (Function) services.getNamespaces().functions().lookup(INDEX_OF);
	assert indexOf != null;
	return indexOf;
    }

    public Function lastIndexOf() {
	final Function lastIndexOf = (Function) services.getNamespaces().functions().lookup(LAST_INDEX_OF);
	assert lastIndexOf != null;
	return lastIndexOf;
    }

    
}
