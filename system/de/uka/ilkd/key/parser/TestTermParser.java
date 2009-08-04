// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.SetAsListOfTaclet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.DefaultExceptionHandler;


public class TestTermParser extends TestCase {
    
    private static final TermFactory tf = TermFactory.DEFAULT;

    private static NamespaceSet nss;

    private static Services serv;

    private static Recoder2KeY r2k;

    private static Sort elem,list;

    private static Function head,tail,nil,cons,isempty,p; 

    private static LogicVariable x,y,z,xs,ys,zs;

    private static Term t_x,t_y,t_z,t_xs,t_ys;
    private static Term t_headxs,t_tailys,t_nil;

    public TestTermParser(String name) {
	super(name);
    }


    public void setUp() {
	if(serv != null) {
	    return;
	}
	serv = TacletForTests.services ();
	nss = serv.getNamespaces();
	nss.sorts().add(Sort.NULL);
	r2k = new Recoder2KeY(serv, nss);
	r2k.parseSpecialClasses();	
	parseDecls("\\sorts { boolean; elem; list; int; int_sort; numbers;  }\n" +
		   "\\functions {\n" +
		   "  elem head(list);\n" +
		   "  list tail(list);\n" +
		   "  list nil;\n" +
		   "  list cons(elem,list);\n"  +
//		   "numbers #;\n"+
//		   "numbers 0 (numbers);\n"+
//		   "numbers 1 (numbers);\n"+
//		   "numbers 2 (numbers);\n"+
//		   "numbers 3 (numbers);\n"+
//		   "numbers 4 (numbers);\n"+
//		   "numbers 5 (numbers);\n"+
//		   "numbers 6 (numbers);\n"+
//		   "numbers 7 (numbers);\n"+
//		   "numbers 8 (numbers);\n"+
//		   "numbers 9 (numbers);\n"+
//		   "numbers neglit (numbers);\n"+
//                   "int Z (numbers);\n"+
//		   "int neg (int);\n"+
//		   "int add (int,int);\n"+
//		   "int sub (int,int);\n"+
//		   "int mul (int,int);\n"+
//		   "int div (int,int);\n"+
//		   "int mod (int,int);\n"+
		   "int aa ;\n"+
		   "int bb ;\n"+
		   "int cc ;\n"+
		   "int dd ;\n"+
		   "int ee ;\n"+
		   "}\n" +
		   "\\predicates {\n" +
//		   "  lt(int,int);\n" +
//                   "  leq(int,int);\n" +
		   "  isempty(list);\n" +
//		   "  p(elem,list);\n" +
		   "}\n"+
		   "\\programVariables {int globalIntPV;}"

		   );
       
        elem = lookup_sort("elem");
	list = lookup_sort("list");

	head = lookup_func("head"); tail = lookup_func("tail");
	nil = lookup_func("nil"); cons = lookup_func("cons");
	isempty = lookup_func("isempty"); p = lookup_func("p");
	
	// The declaration parser cannot parse LogicVariables; these
	// are normally declared in quantifiers, so we introduce them
	// ourselves!
	x = declareVar("x",elem);   t_x = tf.createVariableTerm(x);  
	y = declareVar("y",elem);   t_y = tf.createVariableTerm(y);  
	z = declareVar("z",elem);   t_z = tf.createVariableTerm(z);  
	xs = declareVar("xs",list); t_xs = tf.createVariableTerm(xs);
	ys = declareVar("ys",list); t_ys = tf.createVariableTerm(ys);
	
	t_headxs = tf.createFunctionTerm(head,t_xs);
	t_tailys = tf.createFunctionTerm(tail,t_ys);
	t_nil = tf.createFunctionTerm(nil);
    }

    Sort lookup_sort(String name) {
	return (Sort)nss.sorts().lookup(new Name(name));
    }
    
    Function lookup_func(String name) {
	return (Function)nss.functions().lookup(new Name(name));
    }

    LogicVariable declareVar(String name,Sort sort) {
	LogicVariable v = new LogicVariable(new Name(name),sort);
	nss.variables().add(v);
	return v;
    }
    

    private KeYParser stringDeclParser(String s) {
        // fills namespaces 
        new Recoder2KeY(TacletForTests.services (), nss).parseSpecialClasses();
	return new KeYParser(ParserMode.DECLARATION,new KeYLexer(new StringReader(s),null),
			      "No file. Call of parser from parser/TestTermParser.java",
			      serv, nss);
    }

    public void parseDecls(String s) {
	try {	   
            stringDeclParser(s).decls();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw (RuntimeException) 
                new RuntimeException("Exc while Parsing:\n" + sw ).initCause(e);
	}
    }

    public Term parseProblem(String s) {
	try {	  
	    new Recoder2KeY(TacletForTests.services (), 
	                    nss).parseSpecialClasses();	   
	    return new KeYParser
		(ParserMode.PROBLEM, new KeYLexer(new StringReader(s),null),
		 "No file. Call of parser from parser/TestTermParser.java",
		 new ParserConfig(serv, nss),
		 new ParserConfig(serv, nss),
		 null, SetAsListOfTaclet.EMPTY_SET,null).problem();	    
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}	
    }

    private KeYParser stringTermParser(String s) {
	return new KeYParser
	    (ParserMode.TERM, 
	     new KeYLexer(new StringReader(s), new DefaultExceptionHandler()), 
	     "No file. Call of parser from parser/TestTermParser.java",
	     tf, 
	     r2k,
	     serv, 
	     nss, 
	     new AbbrevMap());

    }

    public Term parseTerm(String s) {
	try {	  
	    return stringTermParser(s).term();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }
    

    public Term parseFma(String s) {
	try {	    	    
	    return stringTermParser(s).formula();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    public void test1() {
	assertEquals("parse x",t_x,parseTerm("x"));
    }

    public void test1a() {
	boolean parsed = false;
	try { parseTerm("x()"); parsed = true;} catch (Exception e) {}
	assertFalse("parse x() should fail", parsed);
    }

    public void test2() {
	assertEquals("parse head(xs)",t_headxs,parseTerm("head(xs)"));
    }

    public void test3() {
	Term t = tf.createFunctionTerm(cons,t_headxs,t_tailys);
	
	assertEquals("parse cons(head(xs),tail(ys))",
		     t,parseTerm("cons(head(xs),tail(ys))"));
    }

    public void test5() {
	Term t = tf.createEqualityTerm
	    (tf.createFunctionTerm
	     (head,
	      tf.createFunctionTerm(cons, t_x, t_xs)),
	     tf.createFunctionTerm
	     (head,
	      tf.createFunctionTerm (cons,t_x,t_nil)));
	     
	assertEquals("parse head(cons(x,xs))=head(cons(x,nil))",
		     t,parseFma("head(cons(x,xs))=head(cons(x,nil))"));
	assertEquals("parse head(cons(x,xs))=head(cons(x,nil))",
		     t,parseFma("head(cons(x,xs))=head(cons(x,nil()))"));
    }

    public void testNotEqual() {
	Term t = tf.createJunctorTerm(Junctor.NOT,
	    tf.createEqualityTerm
	    (tf.createFunctionTerm
	     (head,
	      tf.createFunctionTerm(cons, t_x, t_xs)),
	     tf.createFunctionTerm
	     (head,
	      tf.createFunctionTerm (cons,t_x,t_nil))));
	     
	assertEquals("parse head(cons(x,xs))!=head(cons(x,nil))",
		     t,parseFma("head(cons(x,xs))!=head(cons(x,nil))"));
    }


    public void test6() {
	Term t = tf.createJunctorTerm
	    (Equality.EQV,
	     tf.createJunctorTerm
	     (Junctor.IMP,
	      tf.createJunctorTerm
	      (Junctor.OR,
	       tf.createEqualityTerm(t_x,t_x),
	       tf.createEqualityTerm(t_y,t_y)),
	      tf.createJunctorTerm
	      (Junctor.AND,
	       tf.createEqualityTerm(t_z,t_z),
	       tf.createEqualityTerm(t_xs,t_xs))),
	     tf.createJunctorTerm
	     (Junctor.NOT,
	      tf.createEqualityTerm(t_ys,t_ys)));

	     
	assertEquals("parse x=x | y=y -> z=z & xs =xs <-> ! ys = ys",
		     t,parseFma("x=x|y=y->z=z&xs=xs<->!ys=ys"));
    }

    public void test7() {
	/** Bound variables are newly created by the parser,
	 * so we have to parse first, then extract the used variables,
	 * then build the formulae. */
	
	String s = "\\forall list x; \\forall list l1; ! x = l1";
	Term t = parseFma(s);
	
	LogicVariable thisx = (LogicVariable) t.varsBoundHere(0)
	    .getQuantifiableVariable(0);
	LogicVariable l1 = (LogicVariable) t.sub(0).varsBoundHere(0)
	    .getQuantifiableVariable(0);

	Term t1 = tf.createQuantifierTerm
	    (Quantifier.ALL,thisx,
	     tf.createQuantifierTerm
	     (Quantifier.ALL,l1,
	      tf.createJunctorTerm
	      (Junctor.NOT,
	       tf.createEqualityTerm(tf.createVariableTerm(thisx),
				     tf.createVariableTerm(l1)))));
	
	assertTrue("new variable in quantifier", thisx != x);
	assertEquals("parse \\forall list x; \\forall list l1; ! x = l1", t1,t);
	
    }

    public void test8() {
	/** A bit like test7, but for a substitution term */

	{
	    String s = "{\\subst elem xs; head(xs)} cons(xs,ys)";
	    Term t = parseTerm(s);

	    LogicVariable thisxs = (LogicVariable) t.varsBoundHere(1)
		.getQuantifiableVariable(0);
	
	    Term t1 = tf.createSubstitutionTerm
		(WarySubstOp.SUBST,
		 thisxs, t_headxs,
		 tf.createFunctionTerm
		 (cons, 
		  tf.createVariableTerm(thisxs), 
		  t_ys));

	    assertTrue("new variable in subst term", thisxs != xs);
	    assertEquals("parse {xs:elem head(xs)} cons(xs,ys)",t1,t);
	}
    }

    public void test9() {
	/* Try something with a prediate */
	
	String s = "\\exists list x; !isempty(x)";
	Term t = parseFma(s);
	
	LogicVariable thisx = (LogicVariable) t.varsBoundHere(0)
	    .getQuantifiableVariable(0);

	Term t1 = tf.createQuantifierTerm
	    (Quantifier.EX,thisx,
	     tf.createJunctorTerm
	     (Junctor.NOT,
	      tf.createFunctionTerm(isempty,tf.createVariableTerm(thisx))));
	      
	assertTrue("new variable in quantifier", thisx != x);
	assertEquals("parse \\forall list x; \\forall list l1; ! x = l1", t1,t);
	
    }

    public void test10() {
	// Unquoted, this is
	// <{ int x = 2; {String x = "\"}";} }> true
	//	String s = "< { int x = 1; {String s = \"\\\"}\";} } > true";
	String s = "\\<{ int x = 1; {int s = 2;} }\\> x=x";
	Term t = parseTerm(s);
	
	// for now, just check that the parser doesn't crash
	
	//	 System.out.println(t);

	// Same with a box
	s = "\\[{ int x = 2; {String s = \"\\\"}\";} }\\] true";
	//s = "< { int x = 1; {int s = 2;} } > true";
	t = parseTerm(s);
	//System.out.println(t);
    }
   


    public void test12() {
	    String s="\\<{int i; i=0;}\\> \\<{ while (i>0) ;}\\>true";
	    Term t = parseTerm(s);
    }

    public void test13(){
       Term t1 = parseTerm("\\exists elem x; \\forall list ys; \\forall list xs; ( xs ="
		                    			+" cons(x,ys))");
	Term t2 = parseTerm("\\exists elem y; \\forall list xs; \\forall list ys; ( ys ="
                                        +" cons(y,xs))");
        Term t3 = parseTerm("\\exists int_sort bi; (\\<{ int p_x = 1;"
                            +" {int s = 2;} }\\>"
                            +" true ->"
                            +"\\<{ int p_x = 1;boolean p_y=2<1;"
                            +" while(p_y){ int s=3 ;} }\\>"
                            +" true)");
        Term t4 = parseTerm("\\exists int_sort ci; (\\<{ int p_y = 1;"
                            +" {int s = 2;} }\\>"
                            +" true ->"
                            +"\\<{ int p_y = 1;boolean p_x = 2<1;"
                            +"while(p_x){ int s=3 ;} }\\>"
                            +" true)");
        assertTrue("Terms should be equalModRenaming", t3.equalsModRenaming(t4));
     }

    public void test14() {
	String s="\\<{int[] i;i=new int[5];}\\>true";
	Term t=parseTerm(s);
	s="\\<{int[] i;}\\>\\<{}\\>true";
	t=parseTerm(s);
    }

    public void xtestBindingUpdateTermOldBindingAlternative() {
	String s="\\<{int i,j;}\\> {i:=j} i = j";
	Term t = parseTerm(s);
	assertTrue("expected {i:=j}(i=j) but is ({i:=j}i)=j)", 
		t.sub(0).op() instanceof UpdateApplication);
    }

    public void testBindingUpdateTerm() {
	String s="\\forall jint j; {globalIntPV:=j} globalIntPV = j";
	Term t = parseTerm(s);
	assertFalse("expected ({globalIntPV:=j}globalIntPV)=j) but is {globalIntPV:=j}(globalIntPV=j)", 
		t.sub(0).op() instanceof UpdateApplication);
    }

    public void testParsingArray() {
	String s="\\forall int[][] i; \\forall int j; i[j][j] = j";
	Term t = parseTerm(s);
    }


    public void xtestParsingArrayWithSpaces() {
	String s="\\<{int[][] i; int j;}\\> i[ j ][ j ] = j";
	Term t = parseTerm(s);
    }

    public void testParsingArrayCombination() {
	String s="\\forall int[][] i; \\forall int j; i [i[i[j][j]][i[j][j]]][i[j][i[j][j]]] = j";
	Term t = parseTerm(s);
    }

    
    public void testAmbigiousFuncVarPred() {
	// tests bug id 216
	String s = "\\functions {} \\predicates{mypred(int, int);}"+
	    "\n\\problem {\\forall int x; mypred(x, 0)}\n \\proof {\n"+
	    "(branch \"dummy ID\""+
	    "(opengoal \"  ==> true  -> true \") ) }";
	try {
	    parseProblem(s);
	} catch (RuntimeException re) {
	    System.out.println(re);
	    assertTrue("Fixed bug 216 occured again. The original bug "+
		       "was due to ambigious rules using semantic "+
		       "predicates in a 'wrong' way", false);
	}
    }

    public void testParseQueriesAndAttributes() {
	TacletForTests.getJavaInfo().readJavaBlock("{}");
	r2k.readCompilationUnit("public class T extends "
				+"java.lang.Object{ "
				+"private T a;"
				+"private static T b;"
				+"T c;"
				+"static T d;"
				+"public T e;"
				+"public static T f;"
				+"protected T g;"
				+"protected T h;"
				+"public T query(){} "
				+"public static T staticQ(T p){} "
				+"public static T staticQ() {}}");
	String s = "\\forall T t;( (t.query()=t & t.query@(T)()=t & T.staticQ()=t "
	    +"& T.staticQ(t)=t & T.b=t.a@(T) & T.d=t.c@(T) & t.e@(T)=T.f & t.g@(T)=t.h@(T)))";
	parseTerm(s);
    }

    public void testProgramVariables() {
	TacletForTests.getJavaInfo().readJavaBlock("{}");
	r2k.readCompilationUnit("public class T0 extends "
				+"java.lang.Object{} ");
	String s = "\\<{T0 t;}\\> t(1,2) = t()";
	boolean parsed=false;
	try {
	    parseTerm(s);
	    parsed = true;
	} catch (Exception e) {}
	assertFalse("Program variables should not have arguments", parsed);
    }


    public void testNegativeLiteralParsing() {
	String s1 = "-1234";
	Term t = null;
	try {
	    t = parseTerm(s1);
	} catch (Exception e) {fail();}
	assertTrue("Failed parsing negative literal", 
		   (""+t.op().name()).equals("Z") && 
		   (""+t.sub(0).op().name()).equals("neglit"));


	String s2 = "-(1) ";
	try {
	    t = parseTerm(s2);
	} catch (Exception e) {fail();}
	assertTrue("Failed parsing negative complex term", 
		   (""+t.op().name()).equals("neg") && 
		   (""+t.sub(0).op().name()).equals("Z"));

	String s3 = "\\forall int i; -i = 0 ";
	try {
	    t = parseTerm(s3);
	} catch (Exception e) {fail();}
	assertTrue("Failed parsing negative variable", 
		   (""+t.sub(0).sub(0).op().name()).equals("neg"));

	
    }

    public void testIfThenElse () {
        Term t=null, t2=null;
        
        String s1 = "\\if (3=4) \\then (1) \\else (2)";
        try {
            t = parseTerm ( s1 );
        } catch ( Exception e ) {
            fail ();
        }
        assertTrue ( "Failed parsing integer if-then-else term",
                     t.op () == IfThenElse.IF_THEN_ELSE
                     && t.sub ( 0 ).equals ( parseTerm ( "3=4" ) )
                     && t.sub ( 1 ).equals ( parseTerm ( "1" ) )
                     && t.sub ( 2 ).equals ( parseTerm ( "2" ) ) );

        String s2 = "\\if (3=4 & 1=1) \\then (\\if (3=4) \\then (1) \\else (2)) \\else (2)";
        try {
            t2 = parseTerm ( s2 );
        } catch ( Exception e ) {
            fail ();
        }
        assertTrue ( "Failed parsing nested integer if-then-else term",
                     t2.op () == IfThenElse.IF_THEN_ELSE
                     && t2.sub ( 0 ).equals ( parseTerm ( "3=4 & 1=1" ) )
                     && t2.sub ( 1 ).equals ( t )
                     && t2.sub ( 2 ).equals ( parseTerm ( "2" ) ) );

        String s3 = "\\if (3=4) \\then (1=2) \\else (2=3)";
        try {
            t = parseTerm ( s3 );
        } catch ( Exception e ) {
            fail ();
        }
        assertTrue ( "Failed parsing propositional if-then-else term",
                     t.op () == IfThenElse.IF_THEN_ELSE
                     && t.sub ( 0 ).equals ( parseTerm ( "3=4" ) )
                     && t.sub ( 1 ).equals ( parseTerm ( "1=2" ) )
                     && t.sub ( 2 ).equals ( parseTerm ( "2=3" ) ) );

    }
   

    public void testInfix1() {
	assertEquals("infix1",parseTerm("aa + bb"),
	                      parseTerm("add(aa,bb)"));
    }

    public void testInfix2() {
	assertEquals("infix2",parseTerm("aa + bb*cc"),
	                      parseTerm("add(aa,mul(bb,cc))"));
    }

    public void testInfix3() {
	assertEquals("infix3",parseTerm("aa + bb*cc < 123 + -90"),
	                      parseTerm("lt(add(aa,mul(bb,cc)),add(123,-90))"));
    }

    public void testInfix4() {
	assertEquals("infix4",parseTerm("aa%bb*cc < -123"),
	                      parseTerm("lt(mul(mod(aa,bb),cc),-123)"));
    }
    
    public void testCast() {
        assertEquals("cast stronger than plus", parseTerm("(int)3+2"), 
                parseTerm("((int)3)+2"));
     }
}
