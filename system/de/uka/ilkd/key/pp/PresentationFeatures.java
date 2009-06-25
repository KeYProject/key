// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.Proof;

public class PresentationFeatures {


    private PresentationFeatures() {}


    private static void putInfixNotation(NotationInfo notInfo, 
					 Namespace functions,
					 String op,
					 String token, int prio, int lass, int rass) {
	notInfo.createInfixNotation((Function) functions.lookup(new Name(op)), token, prio, lass, rass);
    }

    private static void putPrefixNotation(NotationInfo notInfo, 
					  Namespace functions,
					  String op,
					  String token) {
	notInfo.createPrefixNotation((Function) functions.lookup(new Name(op)), token);
    }

    public static boolean ENABLED=false;

    public static void modifyNotationInfo(NotationInfo notInfo,
					  Namespace functions) {
	if (ENABLED) {
	    putInfixNotation(notInfo, functions, "lt", "< ", 80, 90, 90);
	    putInfixNotation(notInfo, functions, "gt", "> ", 80, 90, 90);
	    putInfixNotation(notInfo, functions, "leq", "<=", 80, 90, 90);
	    putInfixNotation(notInfo, functions, "geq", ">=", 80, 90, 90);

	    putInfixNotation(notInfo, functions, "sub", "-", 90, 90, 91);
	    putInfixNotation(notInfo, functions, "add", "+", 90, 90, 91);

	    putInfixNotation(notInfo, functions, "mul", "*", 100, 100, 101);
	    putInfixNotation(notInfo, functions, "div", "/", 100, 100, 101);
	    putInfixNotation(notInfo, functions, "mod", "%", 100, 100, 101);
	    putPrefixNotation(notInfo, functions, "neg", "-");
	    notInfo.createNumLitNotation
		((Function)functions.lookup(new Name("Z")));
	    putPrefixNotation(notInfo, functions, "neglit", "-");
	}
    }

    private static StringBuffer printlastfirst(Term t) {
	if (t.op().arity()==0) {
	    return new StringBuffer();
	} else {
	    return printlastfirst(t.sub(0)).
		append(t.op().name().toString());
	}
    }

    public static String printNumberTerm(Term t) 
    {
	if (t.sub(0).op().name().toString().equals("neglit")) {
	    return "-"+
		printlastfirst(t.sub(0).sub(0)).toString();
	} else {
	    return printlastfirst(t.sub(0)).toString();
	}
    }

    public static void initialize(Namespace funcns, NotationInfo ni, Proof p) {
	if (ENABLED) {
	    modifyNotationInfo(ni, funcns);
	    if (p!=null) p.updateProof();
	}	
    }

}
