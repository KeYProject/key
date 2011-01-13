// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.ExtList;


public final class CharListLDT extends LDT {
    
    public static final Name NAME = new Name("CharList");
    
    //Warning: Some names of char list functions are hardcoded into 
    //         LexPathOrdering.
                
    //functions
    private final Function strEmpty;
    private final Function strCat;
    private final Function strCons;
    private final Function strCharAt;
    private final Function strLength;
    private final Function strIndexOfChar;
    private final Function strSub;
    private final Function strConcat;
    private final Function strIndexOfStr;
    private final Function strLastIndexOfChar;
    private final Function strLastIndexOfStr;
    private final Function strReplace;
    private final Function strTranslateInt;
    private final Function strRemoveZeros;
    private final Function strHashCode;

    private final Function strPool;
    private final Function strContent;
    
    //predicates
    private final Function strStartsWith;
    private final Function strEndsWith;
    private final Function strContains;


    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public CharListLDT(Services services) {
	super(NAME, services);
	strEmpty           = addFunction(services, "strEmpty");
	strCat             = addFunction(services, "strCat");
	strCons            = addFunction(services, "strCons");
	strCharAt          = addFunction(services, "strCharAt");
	strLength          = addFunction(services, "strLength");
	strIndexOfChar     = addFunction(services, "strIndexOfChar");
	strSub             = addFunction(services, "strSub");
	strConcat          = addFunction(services, "strConcat");
	strIndexOfStr      = addFunction(services, "strIndexOfStr");
	strLastIndexOfChar = addFunction(services, "strLastIndexOfChar");
	strLastIndexOfStr  = addFunction(services, "strLastIndexOfStr");
	strReplace         = addFunction(services, "strReplace");
	strTranslateInt    = addFunction(services, "strTranslateInt");
	strRemoveZeros     = addFunction(services, "strRemoveZeros");
	strHashCode        = addFunction(services, "strHashCode");

	strPool            = addFunction(services, "strPool");
	strContent         = addFunction(services, "strContent");

	strStartsWith      = addFunction(services, "strStartsWith");
	strEndsWith        = addFunction(services, "strEndsWith");
	strContains        = addFunction(services, "strContains");
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
	return new Character(charVal).toString();
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
    
    public Function getStrEmpty() {
	return strEmpty;
    }
    
    
    public Function getStrCat() {
	return strCat;
    }
    
    
    public Function getStrCons() {
	return strCons;
    }
    
    
    public Function getStrCharAt() {
	return strCharAt;
    }
    
    
    public Function getStrLength() {
	return strLength;
    }
    
    
    public Function getStrIndexOfChar() {
	return strIndexOfChar;
    }
    
    
    public Function getStrSub() {
	return strSub;
    }
    
    
    public Function getStrConcat() {
	return strConcat;
    }
    
    
    public Function getStrIndexOfStr() {
	return strIndexOfStr;
    }
    
    
    public Function getStrLastIndexOfChar() {
	return strLastIndexOfChar;
    }
    
   
    public Function getStrLastIndexOfStr() {
	return strLastIndexOfStr;
    }
    
    
    public Function getStrReplace() {
	return strReplace;
    }
    
    
    public Function getStrTranslateInt() {
	return strTranslateInt;
    }
    
    
    public Function getStrRemoveZeros() {
	return strRemoveZeros;
    }
   
    
    public Function getStrHashCode() {
	return strHashCode;
    }

    
    public Function getStrPool() {
	return strPool;
    }
    
    
    public Function getStrContent() {
	return strContent;
    }
    
    
    public Function getStrStartsWith() {
	return strStartsWith;
    }
    
    
    public Function getStrEndsWith() {
	return strEndsWith;
    }
    
    
    public Function getStrContains() {
	return strContains;
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
	    			 Services services, 
	    			 ExecutionContext ec) {
	return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
	final Term term_empty = TermBuilder.DF.func(strEmpty);

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
	    result = TermBuilder.DF.func(strCons,
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
    public Expression translateTerm(Term t, ExtList children) {
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
