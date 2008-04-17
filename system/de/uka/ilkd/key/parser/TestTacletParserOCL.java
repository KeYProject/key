// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.OCLInvSimplPO;
import de.uka.ilkd.key.rule.TacletForTests;

/** class tests the parser for Taclets
*/


public class TestTacletParserOCL extends TestCase {

    private NamespaceSet nss;
    private Services services;
    private TermFactory tf=TermFactory.DEFAULT;
    private Sort ocl_sort; 
    private TermSymbol forAll, iterate, and, true_, nil;
    private SortedSchemaVariable x, g, coll, expr, init, e1, genExpr;
    private Term nilTerm, trueTerm;

    public TestTacletParserOCL(String name) {
	super(name);
    }

    //
    //  set up
    //

    public void setUp() {
	services = TacletForTests.services();
	InitConfig initConf = new InitConfig();
	OCLInvSimplPO.createNamespaceSetForTests(initConf);

	x = (SortedSchemaVariable)SchemaVariableFactory.createVariableSV(new Name("x"), 
									 OclSort.OCLANY, false);
	initConf.varNS().add(x);

	g = (SortedSchemaVariable)SchemaVariableFactory.createVariableSV(new Name("g"), 
									 OclSort.OCLGENERIC, 
									 false);
	initConf.varNS().add(g);

	genExpr = (SortedSchemaVariable)SchemaVariableFactory.createTermSV(new Name("genExpr"), 
									   OclSort.OCLGENERIC, 
									   false, true, false);
	initConf.varNS().add(genExpr);

	coll = (SortedSchemaVariable)SchemaVariableFactory
	    .createTermSV(new Name("coll"), OclSort.COLLECTION_OF_OCLANY, false, true, false);
	initConf.varNS().add(coll);

	expr = (SortedSchemaVariable)SchemaVariableFactory.createTermSV(new Name("expr"), 
									OclSort.BOOLEAN, 
									false, true, false);
	initConf.varNS().add(expr);

	init = (SortedSchemaVariable)SchemaVariableFactory.createTermSV(new Name("init"), 
									OclSort.OCLGENERIC, 
									false, true, false);
	initConf.varNS().add(init);

	e1 = (SortedSchemaVariable)SchemaVariableFactory.createTermSV(new Name("e1"), 
								      OclSort.OCLANY, 
								      false, true, false);
	initConf.varNS().add(e1);

	forAll = (TermSymbol)initConf.funcNS().lookup(new Name("$forAll"));
	and = (TermSymbol)initConf.funcNS().lookup(new Name("$and"));
	nil = (TermSymbol)initConf.funcNS().lookup(new Name("$empty_set"));
	iterate = (TermSymbol)initConf.funcNS().lookup(new Name("$iterate"));
	true_ = (TermSymbol)initConf.funcNS().lookup(new Name("$true"));

	nss = initConf.namespaces();

	nilTerm = tf.createFunctionTerm(nil);
	trueTerm = tf.createFunctionTerm(true_);
    }


    //
    // Utility Methods for test cases.
    //
    private KeYParser stringTacletParser(String s) {
	return new KeYParser
	    (ParserMode.TACLET,new KeYLexer(new StringReader(s),null), 
	     "No file. parser/TestTacletParser.stringTacletParser("+s+")",  
	     tf, services, nss);
    }

    public Term parseTerm(String s) {
	try {
	    KeYParser p = stringTacletParser(s);
	    return p.term();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }


    //
    // Test cases.
    //

    //Tests OCL operations where one variable gets bound (forAll, exists, select, ...)
    //Only for the problem clause of the .key file, where bound vars are treated as
    //logical vars (not schema vars)
/*
    // WATCHOUT Daniel - this test is wrong
    public void test1() {
	Term tParse = parseTerm("$forAll($empty_set, \\bind OclBoolean s; $and($true, s))");
	LogicVariable this_s  
	    = (LogicVariable)tParse.varsBoundHere(1).getQuantifiableVariable(0);
	ArrayOfQuantifiableVariable[] var = new ArrayOfQuantifiableVariable[2];
	var[0] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[1] = new ArrayOfQuantifiableVariable(new LogicVariable[]{this_s});
	Term tS = tf.createVariableTerm(this_s);
	Term tAnd = tf.createFunctionTerm(and, trueTerm, tS);
	Term term = tf.createFunctionWithBoundVarsTerm(forAll, new Term[]{nilTerm, tAnd}, var);
	assertEquals("parse $forAll($empty_set, \\bind OclBoolean s; $and($true, s))",
		     term,
		     tParse);
	assertTrue(!services.getExceptionHandler().error());
    }
*/

    //Tests the OCL operation where two variables get bound -- iterate
    //Only for the problem clause of the .key file, where bound vars are treated as
    //logical vars (not schema vars)

/*
    // WATCHOUT Daniel - this test is wrong
    public void test2() {
	Term tParse = parseTerm("$iterate($empty_set," +
				"$true, \\bind(OclBoolean s; OclBoolean acc) $and(s, acc))");
	LogicVariable this_s 
	    = (LogicVariable)tParse.varsBoundHere(2).getQuantifiableVariable(0);
	LogicVariable this_acc 
	    = (LogicVariable)tParse.varsBoundHere(2).getQuantifiableVariable(1);
	ArrayOfQuantifiableVariable[] var = new ArrayOfQuantifiableVariable[3];
	var[0] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[1] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[2] = new ArrayOfQuantifiableVariable(new LogicVariable[]{this_s, this_acc});
	Term tS = tf.createVariableTerm(this_s);
	Term tAcc = tf.createVariableTerm(this_acc);
	Term tAnd = tf.createFunctionTerm(and, tS, tAcc);
	Term term = tf.createFunctionWithBoundVarsTerm(iterate, 
						       new Term[]{nilTerm, trueTerm, tAnd}, 
						       var);
	assertEquals("parse $iterate($empty_set," +
			             "$true, \\bind( OclBoolean s; OclBoolean acc) $and(s, acc))",
		     term,
		     tParse);
    }
*/
    //Tests OCL operations where one variable gets bound (forAll, exists, select, ...)
    //Only for the rules clause of the .key file, where bound vars are treated as
    //schema vars (not logical vars)
    public void test3() {
	ArrayOfQuantifiableVariable[] var = new ArrayOfQuantifiableVariable[2];
	var[0] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[1] = new ArrayOfQuantifiableVariable(new SortedSchemaVariable[]{x});
	Term tExpr = tf.createVariableTerm(expr);
	Term tColl = tf.createVariableTerm(coll);
	Term term = tf.createFunctionWithBoundVarsTerm(forAll, 
						       new Term[]{tColl, tExpr}, var);
	assertEquals("parse $forAll(coll, \\bind x; expr)",
		     term,
		     parseTerm("$forAll(coll, \\bind x; expr)"));
    }

    //Tests the OCL operation where two variables get bound -- iterate
    //Only for the rules clause of the .key file, where bound vars are treated as
    //schema vars (not logical vars)
    public void test4() {
	ArrayOfQuantifiableVariable[] var = new ArrayOfQuantifiableVariable[3];
	var[0] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[1] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[2] = new ArrayOfQuantifiableVariable(new SortedSchemaVariable[]{x, g});
	Term tExpr = tf.createVariableTerm(genExpr);
	Term tColl = tf.createVariableTerm(coll);
	Term tInit = tf.createVariableTerm(init);
	Term term = tf.createFunctionWithBoundVarsTerm(iterate, 
						       new Term[]{tColl, tInit, tExpr},
						       var);
	assertEquals("parse $iterate(coll, init, \\bind( x; g) genExpr)",
		     term,
		     parseTerm("$iterate(coll, init, \\bind( x; g) genExpr)"));
    }

    //Tests the syntax of the substitution operator (one substitution)
    public void test5() {
	Term tExpr = tf.createVariableTerm(expr);
	Term tE1 = tf.createVariableTerm(e1);
	Term term = tf.createSubstitutionTerm(Op.SUBST, x, new Term[]{tE1, tExpr});
	assertEquals("parse {x e1}expr",
		     term,
		     parseTerm("{\\subst x; e1}expr"));
    }
}
