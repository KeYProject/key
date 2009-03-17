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

/**
 * Tests matching and application of some OCL taclets (for OCL simplification). 
 */
package de.uka.ilkd.key.rule;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.OCLInvSimplPO;
import de.uka.ilkd.key.util.Debug;

public class TestOCLTaclets extends TestCase {

    private InitConfig initConf;
    private NamespaceSet nss;
    private TermFactory tf=TermFactory.DEFAULT;
    private SortedSchemaVariable x, acc, nonGenX, nonGenAcc, setSV, e1, g1, g2;
    private RuleAppIndex index;
    private Goal goal;

    private RewriteTaclet ocl_iterateSet_step;
    private RewriteTaclet ocl_iterateSet_empty;
    private RewriteTaclet ocl_if_true;
    private RewriteTaclet ocl_equals;

    public TestOCLTaclets(String name) {
	super(name);
    }

    public TestOCLTaclets(String name, boolean b) {
	super(name);
	Debug.ENABLE_DEBUG = b;
    }

    public void setUp() {       
	initConf = new InitConfig();
	OCLInvSimplPO.createNamespaceSetForTests(initConf);

	x = (SortedSchemaVariable)SchemaVariableFactory
	    .createVariableSV(new Name("x"), 
			      new GenericSort(new Name("AnySV")), 
			      false);
	initConf.varNS().add(x);
	acc = (SortedSchemaVariable)SchemaVariableFactory
	    .createVariableSV(new Name("acc"), 
			      new GenericSort(new Name("AnyCollSV")), 
			      false);
	initConf.varNS().add(acc);
	nonGenX = (SortedSchemaVariable)SchemaVariableFactory
	    .createVariableSV(new Name("nonGenX"), 
			      OclSort.OCLANY, 
			      false);
	initConf.varNS().add(nonGenX);
	nonGenAcc = (SortedSchemaVariable)SchemaVariableFactory
	    .createVariableSV(new Name("nonGenAcc"), 
			      OclSort.OCLGENERIC, 
			      false);
	initConf.varNS().add(nonGenAcc);
	e1 = (SortedSchemaVariable)SchemaVariableFactory.createTermSV(new Name("e1"), 
								      OclSort.OCLANY, 
								      false, true, false);
	initConf.varNS().add(e1);
	setSV = (SortedSchemaVariable)SchemaVariableFactory
	    .createTermSV(new Name("setSV"), OclSort.SET_OF_OCLANY, false, true, false);
	initConf.varNS().add(setSV);
	g1 = (SortedSchemaVariable)SchemaVariableFactory.createTermSV(new Name("g1"), 
								      OclSort.OCLGENERIC, 
								      false, true, false);
	initConf.varNS().add(g1);
	g2 = (SortedSchemaVariable)SchemaVariableFactory.createTermSV(new Name("g2"), 
								      OclSort.OCLGENERIC, 
								      false, true, false);
	initConf.varNS().add(g2);
	nss = initConf.namespaces();

	ocl_iterateSet_step = (RewriteTaclet)parseTaclet("ocl_iterateSet_step{\\find($iterate($insert_set(e1,setSV), g1, \\bind( x; acc) g2)) "
          + "\\varcond(\\notFreeIn(x, setSV),\\notFreeIn(x, g1),\\notFreeIn(acc, setSV),\\notFreeIn(acc, g1))" 
	  +"\\replacewith({\\subst x; e1}({\\subst acc; $iterate(setSV, g1, \\bind( x; acc) g2)}g2))};");

	ocl_iterateSet_empty = (RewriteTaclet)
	    parseTaclet("ocl_iterateSet_empty{\\find($iterate($empty_set, g1, \\bind( x; acc) g2)) " +
			"\\replacewith(g1)}");

	ocl_equals = (RewriteTaclet)
	    parseTaclet("ocl_equals{\\find($equals(g1, g1)) \\replacewith($true)};");

	ocl_if_true = (RewriteTaclet)
	    parseTaclet("ocl_if_true{\\find($if($true, g1, g2)) \\replacewith(g1)};");

	SetOfTaclet tacletSet = SetAsListOfTaclet.EMPTY_SET;
	tacletSet = tacletSet.add(ocl_iterateSet_step);
	tacletSet = tacletSet.add(ocl_iterateSet_empty);
	tacletSet = tacletSet.add(ocl_equals);
	tacletSet = tacletSet.add(ocl_if_true);
	TacletIndex tacletIndex = new TacletIndex(tacletSet);
	TacletAppIndex tacletAppIndex = new TacletAppIndex(tacletIndex);
	BuiltInRuleIndex biri = new BuiltInRuleIndex();
	BuiltInRuleAppIndex birai = new BuiltInRuleAppIndex(biri);
	index = new RuleAppIndex(tacletAppIndex, birai);
    }

    public void tearDown() {
        initConf = null;
        nss = null;
        x = null;
        acc = null;
        nonGenX = null;
        nonGenAcc = null;
        setSV = null;
        e1 = null;
        g1 = null;
        g2 = null;
        index = null;
        goal = null;

        ocl_iterateSet_step = null;
        ocl_iterateSet_empty = null;
        ocl_if_true = null;
        ocl_equals = null;
    }
    
    private KeYParser stringTermParser(String s) {
	return new KeYParser(ParserMode.TERM, new KeYLexer(new StringReader(s),null), 
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


    private KeYParser stringTacletParser(String s) {
	return new KeYParser(ParserMode.TACLET,
	     new KeYLexer(new StringReader(s),null), 
	     "No file. parser/TestTacletParser.stringTacletParser("+s+")",  
	     tf, TacletForTests.services(), nss);
    }

    public Taclet parseTaclet(String s) {
	try {
	    KeYParser p = stringTacletParser(s);
	    return p.taclet(SetAsListOfChoice.EMPTY_SET.add(new Choice(new Name("Default"))));
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    public void test1() {
	Term t = parseTerm("$equals(\"set\", \"set\")");
	ListOfTacletApp list = findMatchingTaclets(t);
	TacletApp tacletApp = list.head();
	assertNotNull("Find ocl_equals", tacletApp);
	ListOfGoal goalList = tacletApp.execute(goal, TacletForTests.services());
	goal = goalList.head();
	assertNotNull("Successfully apply ocl_equals", goal);
	Term result = goal.sequent().succedent().getFirst().formula().sub(0);
	Term expected = parseTerm("$true");
	assertEquals("ocl_equals applied to: $equals(\"set\", \"set\")", result, expected);
    }

    public void test2() {
	Term t = parseTerm("$if($true, $false, $true)");
	ListOfTacletApp list = findMatchingTaclets(t);
	TacletApp tacletApp = list.head();
	assertNotNull("Find ocl_if", tacletApp);
	ListOfGoal goalList = tacletApp.execute(goal, TacletForTests.services());
	goal = goalList.head();
	assertNotNull("Successfully apply ocl_if", goal);
	Term result = goal.sequent().succedent().getFirst().formula().sub(0);
	Term expected = parseTerm("$false");
	assertEquals("ocl_if applied to: $if($true, $false, $true)", result, expected);
    }
   
    public void test3() {
	Term t = parseTerm("$iterate($insert_set($true, $empty_set), $false, " +
			   "\\bind(OclBoolean elem; OclBoolean accum) $and(elem, accum))");

	LogicVariable this_elem 
	    = (LogicVariable)t.varsBoundHere(2).getQuantifiableVariable(0);
	LogicVariable this_acc 
	    = (LogicVariable)t.varsBoundHere(2).getQuantifiableVariable(1);

	ListOfTacletApp list = findMatchingTaclets(t);
	TacletApp tacletApp = list.head();
	assertNotNull("Find ocl_iterateSet_step", tacletApp);
	ListOfGoal goalList = tacletApp.execute(goal, TacletForTests.services());
	goal = goalList.head();
	assertNotNull("Successfully apply ocl_iterate_step", goal);
	Term result = goal.sequent().succedent().getFirst().formula().sub(0);

	//Build the expected result term:
	//$and($true, 
	//     $iterate($empty_set, 
	//              $false, 
	//              \elem:OclBoolean\accum:OclBoolean/ $and(elem, accum)))
	Term nilT = parseTerm("$empty_set");
	Term falseT = parseTerm("$false");
	Term trueT = parseTerm("$true");
	Term elemT = TermFactory.DEFAULT.createVariableTerm(this_elem);
	Term accT = TermFactory.DEFAULT.createVariableTerm(this_acc);
	//TermSymbol and = TacletForTests.funcLookup("$and");
	TermSymbol and 
	    = (TermSymbol)initConf.funcNS().lookup(new Name("$and"));
	Term andTerm2 = TermFactory.DEFAULT.createFunctionTerm(and, 
							       new Term[]{elemT, accT});
	//TermSymbol iterate = TacletForTests.funcLookup("$iterate");
	TermSymbol iterate 
	    = (TermSymbol)initConf.funcNS().lookup(new Name("$iterate"));
	ArrayOfQuantifiableVariable[] var = new ArrayOfQuantifiableVariable[3];
	var[0] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[1] = new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);
	var[2] = new ArrayOfQuantifiableVariable(new LogicVariable[]{this_elem, this_acc});
	Term iterateTerm = TermFactory.DEFAULT
	    .createFunctionWithBoundVarsTerm(iterate,
					     new Term[]{nilT, falseT, andTerm2},
					     var);
	Term expected = TermFactory.DEFAULT.createFunctionTerm(and, 
							       new Term[]{trueT, iterateTerm});
    
	assertEquals("ocl_iterate_step applied to: $iterate($insert_set($true, $empty_set), $false, " +
					     "\\bind(OclBoolean elem; OclBoolean accum) $and(elem, accum)", 
		     result, expected);
    }

    public void test4() {
	Term t = parseTerm("$iterate($empty_set, $false, " +
			   "\\bind(OclBoolean elem; OclBoolean accum) $and(elem, accum))");
	ListOfTacletApp list = findMatchingTaclets(t);
	TacletApp tacletApp = list.head();
	assertNotNull("Find ocl_iterateSet_empty", tacletApp);
	ListOfGoal goalList = tacletApp.execute(goal, TacletForTests.services());
	goal = goalList.head();
	assertNotNull("Successfully apply ocl_iterateSet_empty", goal);
	Term result = goal.sequent().succedent().getFirst().formula().sub(0);
	Term expected = parseTerm("$false");
	assertEquals("ocl_iterateSet_empty applied to: $iterate($empty_set, $false, " +
					     "\\bind( OclBoolean elem; OclBoolean acc) $and(elem, acc)", 
		     result, expected);
    }

    //To ensure that variable SVs of a sort A cannot match a logic variable
    //of a sort B, if A is a supersort of B.
    public void test5() {
	index.tacletIndex().remove(index.tacletIndex().lookup("ocl_iterateSet_step"));
	ocl_iterateSet_step = (RewriteTaclet)
	    parseTaclet("ocl_iterateSet_step{\\find($iterate($insert_set(e1,setSV), "
			+ "g1, \\bind(nonGenX; nonGenAcc) g2)) "
                        +"\\varcond(\\notFreeIn(nonGenX, setSV),\\notFreeIn(nonGenX, g1),\\notFreeIn(nonGenAcc, setSV),\\notFreeIn(nonGenAcc, g1))"
          + "\\replacewith({\\subst nonGenX; e1}({\\subst nonGenAcc; $iterate(setSV, g1, \\bind( nonGenX; nonGenAcc) g2)}g2))};");
	index.tacletIndex().add(ocl_iterateSet_step);
	Term t = parseTerm("$iterate($insert_set($true, $empty_set), $false, " +
			   "\\bind(OclBoolean elem; OclBoolean accum) $and(elem, accum))");

	ListOfTacletApp list = findMatchingTaclets(t);
	TacletApp tacletApp = list.head();
	assertNull("Find ocl_iterateSet_step", tacletApp);
    }

    private ListOfTacletApp findMatchingTaclets(Term t) {
	TermSymbol oclWrapper 
	    = (TermSymbol)initConf.funcNS().lookup(new Name("$OclWrapper"));
	//TermSymbol oclWrapper = TacletForTests.funcLookup("$OclWrapper");
	Term term = TermFactory.DEFAULT.createFunctionTerm(oclWrapper, t);
	ConstrainedFormula cf = new ConstrainedFormula(term);
	Semisequent succ = Semisequent.EMPTY_SEMISEQUENT;
	SemisequentChangeInfo info = succ.insertFirst(cf);
	succ = info.semisequent();
	Sequent seq = Sequent.createSuccSequent(succ);
	Proof proof = new Proof(new Services());
	Node node = new Node(proof, seq);
	proof.setRoot(node);
	proof.setSimplifier(new UpdateSimplifier());
	goal = new Goal(node, index);

	//Matching of taclets
	PosInOccurrence pos = 
            new PosInOccurrence(cf, PosInTerm.TOP_LEVEL.down(0), false);
	ListOfTacletApp list 
	    = index.getTacletAppAt(TacletFilter.TRUE,
				   pos,
				   TacletForTests.services(),
				   Constraint.BOTTOM);
	return list;
    }
}
