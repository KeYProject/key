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


package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;


public final class CharListLDT extends LDT {
    
    public static final Name NAME = new Name("CharList");
    
    public static final Name STRINGPOOL_NAME = new Name("strPool");
    public static final Name STRINGCONTENT_NAME = new Name("strContent");
    
    
    //Warning: Some names of char list functions are hardcoded into 
    //         LexPathOrdering and into CharListNotation!
                
    //functions
    private final Function clEmpty;
    private final Function clCat;
    private final Function clCons;
    private final Function clCharAt;
    private final Function clLength;
    private final Function clIndexOfChar;
    private final Function clSub;
    private final Function clConcat;
    private final Function clIndexOfCl;
    private final Function clLastIndexOfChar;
    private final Function clLastIndexOfCl;
    private final Function clReplace;
    private final Function clTranslateInt;
    private final Function clRemoveZeros;
    private final Function clHashCode;

    //predicates
    private final Function clStartsWith;
    private final Function clEndsWith;
    private final Function clContains;


    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public CharListLDT(TermServices services) {
	super(NAME, services);
	clEmpty           = addFunction(services, "clEmpty");
	clCat             = addFunction(services, "clCat");
	clCons            = addFunction(services, "clCons");
	clCharAt          = addFunction(services, "clCharAt");
	clLength          = addFunction(services, "clLength");
	clIndexOfChar     = addFunction(services, "clIndexOfChar");
	clSub             = addFunction(services, "clSub");
	clConcat          = addFunction(services, "clConcat");
	clIndexOfCl       = addFunction(services, "clIndexOfCl");
	clLastIndexOfChar = addFunction(services, "clLastIndexOfChar");
	clLastIndexOfCl   = addFunction(services, "clLastIndexOfCl");
	clReplace         = addFunction(services, "clReplace");
	clTranslateInt    = addFunction(services, "clTranslateInt");
	clRemoveZeros     = addFunction(services, "clRemoveZeros");
	clHashCode        = addFunction(services, "clHashCode");

	clStartsWith      = addFunction(services, "clStartsWith");
	clEndsWith        = addFunction(services, "clEndsWith");
	clContains        = addFunction(services, "clContains");
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
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
	return ""+charVal;
    }
    

    private StringBuffer printlastfirst(Term t) {
	if (t.op().arity() == 0) {
	    return new StringBuffer();
	} else {
	    return printlastfirst(t.sub(0)).append(t.op().name().toString());
	}
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public Function getClEmpty() {
	return clEmpty;
    }
    
    
    public Function getClCat() {
	return clCat;
    }
    
    
    public Function getClCons() {
	return clCons;
    }
    
    
    public Function getClCharAt() {
	return clCharAt;
    }
    
    
    public Function getClLength() {
	return clLength;
    }
    
    
    public Function getClIndexOfChar() {
	return clIndexOfChar;
    }
    
    
    public Function getClSub() {
	return clSub;
    }
    
    
    public Function getClConcat() {
	return clConcat;
    }
    
    
    public Function getClIndexOfCl() {
	return clIndexOfCl;
    }
    
    
    public Function getClLastIndexOfChar() {
	return clLastIndexOfChar;
    }
    
   
    public Function getClLastIndexOfCl() {
	return clLastIndexOfCl;
    }
    
    
    public Function getClReplace() {
	return clReplace;
    }
    
    
    public Function getClTranslateInt() {
	return clTranslateInt;
    }
    
    
    public Function getClRemoveZeros() {
	return clRemoveZeros;
    }
   
    
    public Function getClHashCode() {
	return clHashCode;
    }

        
    public Function getClStartsWith() {
	return clStartsWith;
    }
    
    
    public Function getClEndsWith() {
	return clEndsWith;
    }
    
    
    public Function getClContains() {
	return clContains;
    }

    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                                 Term[] subs, 
                                 Services services, 
                                 ExecutionContext ec) {
	return false;
    }
    

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                		 Term left, 
                		 Term right, 
                		 Services services, 
                		 ExecutionContext ec) {
	return false;
    }

    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
	    			 Term sub, 
	    			 TermServices services, 
	    			 ExecutionContext ec) {
	return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
	final Term term_empty = services.getTermBuilder().func(clEmpty);

	char[] charArray;
	Term result = term_empty;

	if (lit instanceof StringLiteral) {
	    charArray = ((StringLiteral) lit).getValue().toCharArray();
	} else {
	    return null;
	}

	IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
	if (intLDT == null) {
	    throw new IllegalArgumentException(
		    "IntegerLDT is needed for StringLiteral translation");
	}

	for (int i = charArray.length - 2; i >= 1; i--) {
	    result = services.getTermBuilder().func(clCons,
		    intLDT.translateLiteral(new CharLiteral(charArray[i]), 
			                    services),
		    result);
	}

	return result;
    }
    

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return false;
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	final StringBuffer result = new StringBuffer("");
	Term term = t;
	while (term.op().arity() != 0) {
	    result.append(translateCharTerm(term.sub(0)));
	    term = term.sub(1);
	}
	return new StringLiteral("\"" + result + "\"");
    }
    
    
    @Override
    public final Type getType(Term t) {
	assert false;
	return null;
    }
}
