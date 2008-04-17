// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
					 String token) {
	notInfo.createInfixNotation((Function) functions.lookup(new Name(op)), token);
    }

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
	    

	    // ******** For OCL Simplification ************
	    //iterate
	    notInfo.createOCLIterateNotation("iterate");

	    //collection operations with one iteration variable
	    notInfo.createOCLCollOpBoundVarNotation("forAll");
	    notInfo.createOCLCollOpBoundVarNotation("exists");
	    notInfo.createOCLCollOpBoundVarNotation("select");
	    notInfo.createOCLCollOpBoundVarNotation("collect");
	    notInfo.createOCLCollOpBoundVarNotation("reject");
	    notInfo.createOCLCollOpBoundVarNotation("isUnique");
	    notInfo.createOCLCollOpBoundVarNotation("sortedBy");
	    notInfo.createOCLCollOpBoundVarNotation("any");
	    notInfo.createOCLCollOpBoundVarNotation("one");

	    //other collection operations
	    notInfo.createOCLCollOpNotation("asSet");
	    notInfo.createOCLCollOpNotation("includes");
	    notInfo.createOCLCollOpNotation("excludes");
	    notInfo.createOCLCollOpNotation("count");
	    notInfo.createOCLCollOpNotation("includesAll");
	    notInfo.createOCLCollOpNotation("excludesAll");
	    notInfo.createOCLCollOpNotation("isEmpty");
	    notInfo.createOCLCollOpNotation("notEmpty");
	    notInfo.createOCLCollOpNotation("sum");
	    notInfo.createOCLCollOpNotation("union");
	    notInfo.createOCLCollOpNotation("intersection");
	    notInfo.createOCLCollOpNotation("including");
	    notInfo.createOCLCollOpNotation("excluding");
	    notInfo.createOCLCollOpNotation("symmetricDifference");
	    notInfo.createOCLCollOpNotation("asSequence");
	    notInfo.createOCLCollOpNotation("asBag");
	    notInfo.createOCLCollOpNotation("append");
	    notInfo.createOCLCollOpNotation("prepend");
	    notInfo.createOCLCollOpNotation("subSequence");
	    notInfo.createOCLCollOpNotation("at");
	    notInfo.createOCLCollOpNotation("first");
	    notInfo.createOCLCollOpNotation("last");
	    notInfo.createOCLCollOpNotation("size");

	    //non-infix operations on OclType, OclAny, Real, Integer, String 
	    notInfo.createOCLDotOpNotation("allSubtypes");
	    notInfo.createOCLDotOpNotation("allInstances");
	    notInfo.createOCLDotOpNotation("name");
	    notInfo.createOCLDotOpNotation("attributes");
	    notInfo.createOCLDotOpNotation("associationEnds");
	    notInfo.createOCLDotOpNotation("operations");
	    notInfo.createOCLDotOpNotation("supertypes");
	    notInfo.createOCLDotOpNotation("allSupertypes");
	    notInfo.createOCLDotOpNotation("oclIsKindOf");
	    notInfo.createOCLDotOpNotation("oclIsTypeOf");
	    notInfo.createOCLDotOpNotation("oclAsType");
	    notInfo.createOCLDotOpNotation("oclIsNew");
	    notInfo.createOCLDotOpNotation("evaluationType");
	    notInfo.createOCLDotOpNotation("abs");
	    notInfo.createOCLDotOpNotation("floor");
	    notInfo.createOCLDotOpNotation("round");
	    notInfo.createOCLDotOpNotation("max");
	    notInfo.createOCLDotOpNotation("min");
	    notInfo.createOCLDotOpNotation("div");
	    notInfo.createOCLDotOpNotation("mod");
	    notInfo.createOCLDotOpNotation("concat");
	    notInfo.createOCLDotOpNotation("toUpper");
	    notInfo.createOCLDotOpNotation("toLower");
	    notInfo.createOCLDotOpNotation("substring");

	    //prefix
	    notInfo.createOCLPrefixNotation("not", "not "  ,80,80);
	    notInfo.createOCLPrefixNotation("minusPrefix", "-"  ,80,80);

	    //infix
	    notInfo.createOCLInfixNotation("times", "*"  ,70,70,80);
	    notInfo.createOCLInfixNotation("divInfix", "/"  ,70,70,80);
	    notInfo.createOCLInfixNotation("plus", "+"  ,60,60,70);
	    notInfo.createOCLInfixNotation("minus", "-"  ,60,60,70);
	    notInfo.createOCLInfixNotation("lessThan", "<"  ,50,50,60);
	    notInfo.createOCLInfixNotation("lessThanEq", "<="  ,50,50,60);
	    notInfo.createOCLInfixNotation("greaterThan", ">"  ,50,50,60);
	    notInfo.createOCLInfixNotation("greaterThanEq", ">="  ,50,50,60);
	    notInfo.createOCLInfixNotation("equals", "="  ,40,40,50);
	    notInfo.createOCLInfixNotation("notEquals", "<>"  ,40,40,50);
	    notInfo.createOCLInfixNotation("and", "and"  ,30,30,40);
	    notInfo.createOCLInfixNotation("or", "or"  ,30,30,40);
	    notInfo.createOCLInfixNotation("xor", "xor"  ,30,30,40);
	    notInfo.createOCLInfixNotation("implies", "implies"  ,20,20,30);

	    //others
	    notInfo.createOCLWrapperNotation("OclWrapper");
	    notInfo.createOCLCollectionNotation("insert_collection", "Collection");
	    notInfo.createOCLCollectionNotation("insert_set", "Set");
	    notInfo.createOCLCollectionNotation("insert_bag", "Bag");
	    notInfo.createOCLCollectionNotation("insert_sequence", "Sequence");
	    notInfo.createConstantNotation("empty_collection", "Collection{}");
	    notInfo.createConstantNotation("empty_set", "Set{}");
	    notInfo.createConstantNotation("empty_bag", "Bag{}");
	    notInfo.createConstantNotation("empty_sequence", "Sequence{}");
	    notInfo.createConstantNotation("self", "self");
	    notInfo.createConstantNotation("true", "true");
	    notInfo.createConstantNotation("false", "false");
	    notInfo.createOCLIfNotation("if");
	    notInfo.createOCLInvariantNotation("invariant");
	    notInfo.createOCLListOfInvariantsNotation("cons_inv");
	    //
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
	StringBuffer sb=new StringBuffer();
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
