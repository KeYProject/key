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


package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.NoFindTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.SuccTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.AntecTacletBuilder;
import java.io.PrintWriter;
import java.io.StringWriter;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.*;

/** class tests the parser for Taclets
*/


public class TestTacletParser extends TestCase {


    public NamespaceSet nss;
    public Services services;

    TermFactory tf=TermFactory.DEFAULT;

    public TestTacletParser(String name) {
	super(name);
    }

    //
    //  set up
    //

    @Override
    public void setUp() {
	nss =new NamespaceSet();
	services = TacletForTests.services();

	parseDecls("\\sorts { s; }\n" +
		   "\\functions {\n" +
		   "  s f(s);\n" +
		   "}\n" +
		   "\\schemaVariables {\n" +
		   "  \\formula b,b0,post;\n" +
		   "  \\program Statement #p1, #s ; \n" +
		   "  \\program Expression #e2, #e ; \n" +
		   "  \\program SimpleExpression #se ; \n" +
		   "  \\program Variable #slhs, #arr, #ar, #ar1 ; \n" +
		   "  \\program LoopInit #i ; \n"+
                   "  \\program Label #lab, #lb0, #lb1 ; \n"+
                   "  \\program Label #inner, #outer ; \n"+
		   "  \\program Type #typ ; \n"+
		   "  \\program Variable #v0, #v, #v1, #k, #boolv ; \n"+
		   "  \\program[list] Catch #cf ; \n"+
		   "  \\term s x,x0 ;\n" +		
		   "  \\skolemTerm s sk ;\n" +
		   "  \\variables s z,z0 ;\n" +
		   "}\n"
		   );
    }

    //
    // Utility methods for setUp:
    //
    
    Operator lookup_var(String name) {
	return (Operator)nss.variables().lookup(new Name(name));
    }
    

    private KeYParserF stringDeclParser(String s) {
	return new KeYParserF(ParserMode.DECLARATION, new KeYLexerF(s, null),
			      "No file. parser/TestTacletParser.stringDeclParser("+s+")",  
			       services, nss);
    }

    public void parseDecls(String s) {
	try {
	    KeYParserF p = stringDeclParser(s);
	    p.decls();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    //
    // Utility Methods for test cases.
    //
    private KeYParserF stringTacletParser(String s) {
	return new KeYParserF
	    (ParserMode.TACLET,new KeYLexerF(s, null),
	     "No file. parser/TestTacletParser.stringTacletParser("+s+")",  
	     services, nss);
    }

    public Term parseTerm(String s) {
	try {
	    KeYParserF p = stringTacletParser(s);
	    return p.term();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }


    public Term parseFma(String s) {
	try {
	    KeYParserF p = stringTacletParser(s);
	    
	    return p.formula();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    public SequentFormula cf(String s) {
	return new SequentFormula(parseFma(s));
    }
    
    public Semisequent sseq(String s) {
	return Semisequent.EMPTY_SEMISEQUENT.insertFirst(cf(s)).semisequent();
    }
    
    public Sequent sequent(String a,String s) {
	Semisequent ass = Semisequent.EMPTY_SEMISEQUENT;
	Semisequent sss = Semisequent.EMPTY_SEMISEQUENT;
	if ( a != null ) {
	    ass = sseq(a);
	}
	if ( s != null ) {
	    sss = sseq(s);
	}
	return Sequent.createSequent(ass,sss);
    }
    
    Taclet parseTaclet(String s) {
	try {
	    KeYParserF p = stringTacletParser(s);
	    
	    return p.taclet(DefaultImmutableSet.<Choice>nil());
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
 
    public void testImpLeft() {
	// imp-left rule
	// find(b->b0 =>) replacewith(b0 =>) replacewith(=> b) 
	AntecTacletBuilder builder=new AntecTacletBuilder();
	builder.setFind(parseFma("b->b0"));
	builder.setName(new Name("imp_left"));
	builder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      ImmutableSLList.<Taclet>nil(),
				      sequent("b0",null)));
	
	builder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      ImmutableSLList.<Taclet>nil(),
				      sequent(null,"b")));
	
	Taclet impleft=builder.getAntecTaclet();
	String impleftString=
	    "imp_left{\\find(b->b0 ==>) \\replacewith(b0 ==>); \\replacewith(==> b)}";
   	assertEquals("imp-left",impleft,parseTaclet(impleftString));
    }
    
    public void testImpRight() {
	// imp-right rule
	// find(=> b->b0) replacewith(b => b0) 
	SuccTacletBuilder builder=new SuccTacletBuilder();
	builder.setFind(parseFma("b->b0"));
	builder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      ImmutableSLList.<Taclet>nil(),
				      sequent("b","b0")));
	builder.setName(new Name("imp_right"));
	Taclet impright=builder.getSuccTaclet();
	String imprightString=
	    "imp_right{\\find(==> b->b0) \\replacewith(b ==> b0)}";
	
 	assertEquals("imp-right",impright,parseTaclet(imprightString));
    }
    
    public void testCut() {
	// cut rule
	// add(b=>) add(=>b)
	NoFindTacletBuilder builder=new NoFindTacletBuilder();
	builder.addTacletGoalTemplate(new
	    TacletGoalTemplate(sequent("b",null),
			     ImmutableSLList.<Taclet>nil()
			     ));
	
	builder.addTacletGoalTemplate(new
	    TacletGoalTemplate(sequent(null,"b"),
			     ImmutableSLList.<Taclet>nil()
			     ));
	builder.setName(new Name("cut"));
	
       	Taclet cut=builder.getNoFindTaclet();
	String cutString = "cut{\\add(b==>); \\add(==>b)}";
	assertEquals("cut",cut,parseTaclet(cutString));
    }

    public void testClose() {
	// close rule
	// if (b=>) find(=>b) 
	SuccTacletBuilder builder=new SuccTacletBuilder();
	builder.setFind(parseFma("b"));
	builder.setIfSequent(sequent("b",null));
	builder.setName(new Name("close_goal"));
       	Taclet close=builder.getSuccTaclet();
	String closeString = "close_goal{\\assumes (b==>) \\find(==>b) \\closegoal}";
	assertEquals("close",close,
		     parseTaclet(closeString));
    }

    public void testContraposition() {
	// contraposition rule
	// find(b->b0) replacewith(-b0 -> -b)

	RewriteTacletBuilder builder=new RewriteTacletBuilder();
	builder.setFind(parseFma("b->b0"));
	builder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      ImmutableSLList.<Taclet>nil(),
				      parseFma("!b0->!b")));
	builder.setName(new Name("contraposition"));
       	Taclet contraposition=builder.getRewriteTaclet();
	String contrapositionString=
	    "contraposition{\\find(b->b0) \\replacewith(!b0 -> !b)}";

	assertEquals("contraposition",contraposition,
		     parseTaclet(contrapositionString));
    }

    public void testAllRight() {
	// all-right rule
	// find (==> all z.b) varcond ( sk new depending on b ) replacewith (==> {z sk}b)
 	SuccTacletBuilder builder=new SuccTacletBuilder();
	
	builder.setFind(parseFma("\\forall z; b"));
	builder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      ImmutableSLList.<Taclet>nil(),
				      sequent(null,"{\\subst z; sk}b")));
	builder.addVarsNewDependingOn ( (SchemaVariable)lookup_var("sk"),
					(SchemaVariable)lookup_var("b") );
	builder.setName(new Name("all_right"));
       	Taclet allright=builder.getSuccTaclet();
	String allrightString=
	    "all_right{\\find (==> \\forall z; b) \\varcond ( \\new(sk,\\dependingOn(b)) ) \\replacewith (==> {\\subst z; sk}b)}";
	assertEquals("all-right",allright,
		     parseTaclet(allrightString));
    }
    
    public void testAllLeft() {
	// all-left rule
	// find(all z . b==>) add({z x}b==>)
 	AntecTacletBuilder builder=new AntecTacletBuilder();

	builder.setFind(parseFma("\\forall z; b"));
			       
	
	builder.addTacletGoalTemplate(new
	    TacletGoalTemplate(sequent("{\\subst z; x}b",null),
			     ImmutableSLList.<Taclet>nil()));
	builder.setName(new Name("all_left"));
       	Taclet allleft=builder.getAntecTaclet();
	String allleftString = 
	    "all_left{\\find(\\forall z; b==>) \\add({\\subst z; x}b==>)}";
	assertEquals("all-left",allleft,
		     parseTaclet(allleftString));
    }

    public void testExConjSplit() {
 	//exists-conj-split rule
	//find(ex z . ( b & b0 )) varcond(z not free in b) 
	//  replacewith( b & ex z.b0 )
	
	RewriteTacletBuilder builder=new RewriteTacletBuilder();
	builder.setFind(parseFma("\\exists z; (b & b0)"));
	builder.addVarsNotFreeIn((SchemaVariable)lookup_var("z"),
				   (SchemaVariable)lookup_var("b"));
	builder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    ImmutableSLList.<Taclet>nil(),
				    parseFma("b & \\exists z; b0")));
	builder.setName(new Name("exists_conj_split"));
	Taclet exconjsplit = builder.getRewriteTaclet();
	String exconjsplitString = "exists_conj_split{"
	    + "\\find(\\exists z; ( b & b0 )) \\varcond(\\notFreeIn(z, b)) \n"
	    +"\\replacewith( b & \\exists z; b0 )}";
	assertEquals("ex-conj-split",exconjsplit,
		     parseTaclet(exconjsplitString));
    }

    public void testFIdempotent() {
 	// f-idempotent-rule
	// find(f(f(x))) replacewith( f(x) )
	
	RewriteTacletBuilder builder=new RewriteTacletBuilder();

	builder.setFind(parseTerm("f(f(x))"));
	builder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    ImmutableSLList.<Taclet>nil(),
				    parseTerm("f(x)")));
	builder.setName(new Name("f_idempotent"));
	Taclet fidempotent = builder.getRewriteTaclet();
	String fidempotentString = 
	    "f_idempotent{\\find(f(f(x))) \\replacewith(f(x))}";
	assertEquals("f-idempotent",fidempotent,
		     parseTaclet(fidempotentString));
    }

    public void testMakeInsertEq() {
	// make-insert-eq rule
	// find (x = x0 =>) addrules ( find (x) replacewith (x0) )
	RewriteTacletBuilder insertbuilder=new RewriteTacletBuilder();
	insertbuilder.setFind(parseTerm("x"));
	insertbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    ImmutableSLList.<Taclet>nil(),
				    parseTerm("x0")));
	insertbuilder.setName(new Name("insert_eq"));
	Taclet inserteq = insertbuilder.getTaclet();
	
	AntecTacletBuilder builder = new AntecTacletBuilder();
	
	builder.setFind(parseFma("x=x0"));
	builder.addTacletGoalTemplate(new
	    TacletGoalTemplate(Sequent.EMPTY_SEQUENT,
			     ImmutableSLList.<Taclet>nil().prepend(inserteq)));
	builder.setName(new Name("make_insert_eq"));
	Taclet makeinserteq = builder.getAntecTaclet();
	String makeinserteqString = "make_insert_eq"
	    +"{\\find (x = x0 ==>)"
	    + "\\addrules ( insert_eq{\\find (x) \\replacewith (x0)} )}";
	assertEquals("make-insert-eq",makeinserteq,
		     parseTaclet(makeinserteqString));
    }

    public void testSchemaJava0()  {
	
	    parseTaclet("while_right { \\find (\\<{.. while(#e2) {#p1} ...}\\>post)"
	    +"\\replacewith (\\<{.. #unwind-loop (#inner, #outer, while(#e2) {#p1});  ...}\\>post) } ");

    }

    public void testSchemaJava4() {
	FindTaclet taclet=	(FindTaclet) parseTaclet("variable_declaration{ \\find (\\<{.. #typ #v0; ...}\\>post)"
		  +" \\replacewith (\\<{.. #typ #v0; if (true); ...}\\>post)	}");
	Term find=taclet.find();
	JavaBlock jb=find.javaBlock();

	ContextStatementBlock ct=(ContextStatementBlock)jb.program();
	LocalVariableDeclaration lvd=(LocalVariableDeclaration)ct.getChildAt(0);
	VariableSpecification vs=(VariableSpecification)lvd.getChildAt(1);

    }

    public void testVarcondNew() {
	FindTaclet taclet = 
            (FindTaclet) parseTaclet("xy{ \\find (true) \\varcond(\\new(#boolv,long)) \\replacewith(true)}");

	taclet = (FindTaclet) parseTaclet("xy{ \\find (true) \\varcond (\\new(#v0, \\typeof(#e2))) \\replacewith(true)}");

    }

    public void testSchemaJava6() {
	FindTaclet taclet=	(FindTaclet) parseTaclet("xy{ \\find (\\<{.. boolean #boolv; ...}\\>post)"
		  +" \\replacewith (\\<{.. if (true); ...}\\>post)	}");
	Term find=taclet.find();
	JavaBlock jb=find.javaBlock();

	ContextStatementBlock ct=(ContextStatementBlock)jb.program();
	LocalVariableDeclaration lvd=(LocalVariableDeclaration)ct.getChildAt(0);
	VariableSpecification vs=(VariableSpecification)lvd.getChildAt(1);
    }

   

    public void testSchemaJava8() {
	FindTaclet taclet=	(FindTaclet) parseTaclet
	    ("break_test {\\find(\\<{.. #lb0:{ break #lb1; } ...}\\>post)"+ 
	     " \\replacewith (\\<{..  ...}\\>post)}"); 
	Term find=taclet.find();
	JavaBlock jb=find.javaBlock();
	ContextStatementBlock ct=(ContextStatementBlock)jb.program();
    }

    public void testSchemaJava10() {
	FindTaclet taclet=	(FindTaclet) parseTaclet
	    ("array_test {\\find(\\<{..#arr[#e][#e2]=#e2;...}\\>true) \\replacewith (true)}");
	Term find=taclet.find();
	JavaBlock jb=find.javaBlock();
	ContextStatementBlock ct=(ContextStatementBlock)jb.program();
	CopyAssignment ca=(CopyAssignment)ct.getChildAt(0);
	ArrayReference ar=(ArrayReference)ca.getChildAt(0);
	for (int i=0; i<2; i++) {
	    assertTrue(ar.getChildAt(i)!=null);
	}
	ar = (ArrayReference)ar.getChildAt(0);
	for (int i=0; i<2; i++) {
	    assertTrue(ar.getChildAt(i)!=null);
	}
    }

    public void testSchemaJava11(){
	    FindTaclet taclet= 
			(FindTaclet) parseTaclet("eval_order_array_access_right{"+
						 " \\find(\\<{..#v=#ar[#e];...}\\>post)"+
						 "\\varcond(\\new(#ar1,\\typeof(#ar)),"+
						 "\\new(#v0,\\typeof(#e)), \\new(#k, \\typeof(#e)))"+
						 "\\replacewith(\\<{..for(#k=0;#k<#length-reference(#ar);#k++){"+
						 "#ar1[#k]=#ar[#k];}"+
						 "#v0=#e; #v=#ar1[#v0];...}\\>post)"+
						 "\\displayname \"eval_order_array_access_right\"};");
    }

		
    public void testFreeReplacewithVariables () {
        // broken taclet with free variable SV in replacewith
        // buggy { find(==>b) replacewith(==>b,z=z) }

        String brokenTacletString = "buggy { \\find(==>b)" +
                                    "\\replacewith(==>b,z=z) }";
        boolean builderExceptionThrown = false;
        try {
            stringTacletParser(brokenTacletString)
                    .taclet(DefaultImmutableSet.<Choice>nil());
        } catch ( Exception e ) {
            assertTrue ( "Expected IllegalArgumentException, but got " + e,
                         e instanceof IllegalArgumentException );
            builderExceptionThrown = true;
        }
        assertTrue ( "Expected the taclet builder to throw an exception " +
                     "because of free variables in replacewith",
                     builderExceptionThrown );
    }


    //Following tests should work, if parser didn't exit system but propagated 
    // exceptions until here.

    public void testSchemaJava1()  {
	boolean thrown = false;
	try {
	    parseTaclet("xyz { find (<{.. int j=0; for(#i;j<9;j++)"+
	    "; ...}>post)"
		      +"replacewith (<{.. #unwind-loop (while(#e2) {#p1});"+
		      "  ...}>post) } ");
	} catch (RuntimeException e) {
	    thrown = true;
	}
	assertTrue("forinit only valid in initializer of for", thrown);
	}


    public void testSchemaJava2()  {
	boolean thrown=false;
	try {
	    parseTaclet("xyz { find (<{.. int j=0; for(#lab;j<42;j++) ; ...}>post)"
		      +"replacewith (<{.. #unwind-loop (while(#e2) {#p1});  ...}>post) } ");
	} catch (RuntimeException e) {
	    thrown=true;
	}
	assertTrue("label SV not valid here", thrown);
    }

    //more SchemaJava tests are in ../rule/TestMatchTaclet

}
