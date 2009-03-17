// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.OCLInvSimplPO;
import de.uka.ilkd.key.rule.TacletForTests;


public class TestTermParserOCL extends TestCase {
    
    private TermFactory tf = TermFactory.DEFAULT;
    private NamespaceSet nss;
    private Choice defaultChoice;
    private Sort oclAny, oclBoolean; 
    private TermSymbol iterate, true_, false_, cons, nil, and, forAll, oclWrapper;
    private LogicVariable s, i;
    private Term nilTerm, trueTerm, falseTerm;

    public TestTermParserOCL(String name) {
	super(name);
    }

    public void setUp() {
	InitConfig initConf = new InitConfig();
	OCLInvSimplPO.createNamespaceSetForTests(initConf);
	nss = initConf.namespaces();

	forAll = (TermSymbol)initConf.funcNS().lookup(new Name("$forAll"));
	and = (TermSymbol)initConf.funcNS().lookup(new Name("$and"));
	cons = (TermSymbol)initConf.funcNS().lookup(new Name("$insert_set"));
	nil = (TermSymbol)initConf.funcNS().lookup(new Name("$empty_set"));
	iterate = (TermSymbol)initConf.funcNS().lookup(new Name("$iterate"));
	true_ = (TermSymbol)initConf.funcNS().lookup(new Name("$true"));
	false_ = (TermSymbol)initConf.funcNS().lookup(new Name("$false"));
	oclWrapper = (TermSymbol)initConf.funcNS().lookup(new Name("$OclWrapper"));

	nilTerm = tf.createFunctionTerm(nil);
	trueTerm = tf.createFunctionTerm(true_);
	falseTerm = tf.createFunctionTerm(false_);
    }

    private KeYParser stringTermParser(String s) {
	return new KeYParser(ParserMode.TERM,new KeYLexer(new StringReader(s),null), 
			      "No file. Call of parser from parser/TestTermParser.java",
			      tf, 
			      new Recoder2KeY(TacletForTests.services(), nss),
			      TacletForTests.services(), nss, 
			      new AbbrevMap());
    }

    public Term parseTerm(String s) {
	try {
	    KeYParser p = stringTermParser(s);
	    return p.term();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    //Tests OCL operators/operations without any bound variables
    public void test1() {
	Term term = tf.createFunctionTerm(and, trueTerm, falseTerm);
	assertEquals("parse $and($true, $false)",
		     term,
		     parseTerm("$and($true, $false)"));
    }


    //Doesn't work as long as logic/Term::equals() checks "sort() == t.sorts()"
    //instead of "sort().equals(t.sort())".

    //Tests OCL operations where one variable gets bound (forAll, exists, select, ...)
    //Only for the problem clause of the .key file, where bound vars are treated as
    //logical vars (not schema vars)
    public void test2() { 
	Term tParse = parseTerm("$forAll($insert_set($true, $insert_set($false, $empty_set))," + 
				"\\bind OclBoolean s; $and($true, s))"); 
	LogicVariable this_s  
	    = (LogicVariable)tParse.varsBoundHere(1).getQuantifiableVariable(0);
	ArrayOfQuantifiableVariable[] var = new ArrayOfQuantifiableVariable[2];
	var[0] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[1] = new ArrayOfQuantifiableVariable(new LogicVariable[]{this_s});
	Term tS = tf.createVariableTerm(this_s); 
	Term t1Cons = tf.createFunctionTerm(cons, new Term[]{falseTerm, nilTerm}); 
	Term tCons = tf.createFunctionTerm(cons, new Term[]{trueTerm, t1Cons}); 
	Term tAnd = tf.createFunctionTerm(and, trueTerm, tS); 
	Term term = tf.createFunctionWithBoundVarsTerm(forAll, new Term[]{tCons, tAnd}, var); 
	assertEquals("parse $forAll($insert_set($true, $insert_set($false, $empty_set))," + 
				"\\bind OclBoolean s; $and($true, s))", 
		     term, 
		     tParse); 
    }

    //Tests the OCL operation where two variables get bound -- iterate
    //Only for the problem clause of the .key file, where bound vars are treated as
    //logical vars (not schema vars)
    public void test3() { 
	Term tParse = parseTerm("$iterate($insert_set($true, $insert_set($false, $empty_set))," + 
				"$false, \\bind(OclBoolean s; OclBoolean acc) $and(s, acc))"); 
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
	Term t1Cons = tf.createFunctionTerm(cons, new Term[]{falseTerm, nilTerm}); 
	Term tCons = tf.createFunctionTerm(cons, new Term[]{trueTerm, t1Cons}); 
	Term tAnd = tf.createFunctionTerm(and, tS, tAcc); 
	Term term = tf.createFunctionWithBoundVarsTerm(iterate,  
						       new Term[]{tCons, falseTerm, tAnd},
						       var); 
	assertEquals("parse $iterate($insert_set($true, $insert_set($false, $empty_set))," + 
			             "$false, \\bind(OclBoolean s; OclBoolean acc) $and(s, acc))", 
		     term, 
		     tParse); 
    }

}
