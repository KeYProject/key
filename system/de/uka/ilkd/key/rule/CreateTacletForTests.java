// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;


import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;


/** 
 * create Taclet for test cases.
 */
public class CreateTacletForTests extends TestCase {

    Sort nat;

    public static AntecTaclet impleft;
    public static SuccTaclet impright;
    public static SuccTaclet imprightadd;
    public static AntecTaclet notleft;
    public static SuccTaclet notright;
    public static SuccTaclet close;
    public static SuccTaclet allright;
    public static AntecTaclet allleft;
    public static RewriteTaclet contradiction;
    public static NoFindTaclet cut;
    public static RewriteTaclet predsuccelim;
    public static RewriteTaclet pluszeroelim;
    public static RewriteTaclet zeropluselim;
    public static RewriteTaclet succelim;
    public static RewriteTaclet switchsecondsucc;
    public static RewriteTaclet switchfirstsucc;
    public static SuccTaclet closewitheq;

    static Function func_0;
    static Function func_eq;
    static Function func_plus;
    static Function func_min1;
    static Function func_plus1;
    static Function func_p; // Sort.FORMULA

    static Sequent seq_test1;
    static Sequent seq_test2;
    static Sequent seq_test3;
    public static Sequent seq_testNat;
    static Sequent seq_testAll;

    static SchemaVariable b;
    static SchemaVariable x;
    static SchemaVariable x0;
    static SchemaVariable t0;
    static LogicVariable z;
    static Sort sort1;
    static TermFactory tf=TermFactory.DEFAULT;

    static NamespaceSet nss;

    public Services services;

    public CreateTacletForTests(String name) {
	super(name);
	services = new Services();
    }


    public void createTaclets() {
	impleft = (AntecTaclet) parseTaclet
	    ("imp_left{\\find(b->b0==>) \\replacewith(b0==>); \\replacewith(==> b)}");
	impright = (SuccTaclet) parseTaclet
	    ("imp_right{\\find(==> b->b0) \\replacewith(b ==> b0)}");
	notleft = (AntecTaclet) parseTaclet
	    ("not_left{\\find(not b==>) \\replacewith(==>b)}");
	notright = (SuccTaclet) parseTaclet
	    ("not_right{\\find(==>not b) \\replacewith(b==>)}");
	cut = (NoFindTaclet) parseTaclet
	    ("cut{\\add(b==>); \\add(==>b)}");
	imprightadd = (SuccTaclet) parseTaclet
	    ("imp_right_add{\\find(==> b->b0) \\replacewith(b==>b0) \\addrules("
	     + "cut{\\add(b==>); \\add(==>b)})}");
	close = (SuccTaclet) parseTaclet
	    ("close_goal{\\assumes (b==>) \\find(==>b) \\closegoal}");
	contradiction = (RewriteTaclet) parseTaclet
	    ("contracdiction{\\find(b->b0) \\replacewith(!b0 -> !b)}");
	allright = (SuccTaclet) parseTaclet
	    ("all_right{\\find (==> \\forall z; b) \\varcond ( \\new(x,\\dependingOn(b)) ) \\replacewith (==> {\\subst z; x}b)}");
	allleft = (AntecTaclet) parseTaclet
	    ("all_left{\\find(\\forall z; b==>) \\add({\\subst z; x}b==>)}");

    }


    public void createNatTaclets() {
	//decls for nat
	func_0=new RigidFunction(new Name("zero"),nat,new Sort[]{});
	func_eq=new RigidFunction(new Name("="),Sort.FORMULA,
				      new Sort[]{nat,nat});
	func_plus=new RigidFunction(new Name("+"),nat,
					new Sort[]{nat,nat});
	func_min1=new RigidFunction(new Name("pred"),nat,new Sort[]{nat});
	func_plus1=new RigidFunction(new Name("succ"),nat,new Sort[]{nat});

	nss.functions().add(func_0);
	nss.functions().add(func_eq);
	nss.functions().add(func_plus);
	nss.functions().add(func_min1);
	nss.functions().add(func_plus1);

	SchemaVariable var_rn = SchemaVariableFactory.createTermSV(new Name("rn"),nat, false);
	SchemaVariable var_rm = SchemaVariableFactory.createTermSV(new Name("rm"),nat, false);

	Term t_rn = tf.createFunctionTerm((SortedSchemaVariable)var_rn,new Term[]{});
	Term t_rm = tf.createFunctionTerm((SortedSchemaVariable)var_rm,new Term[]{});
	Term t_0 = tf.createFunctionTerm(func_0,new Term[]{});	
	Term t_rnminus1=tf.createFunctionTerm(func_min1,new Term[]{t_rn});
	Term t_rnminus1plus1=tf.createFunctionTerm(func_plus1,
						   new Term[]{t_rnminus1});
	Term t_rneq0=tf.createFunctionTerm(func_eq,new Term[]{t_rn,t_0});
	//	Term t_0minus1=tf.createFunctionTerm(func_min1,
	//		     new Term[]{t_0});
	Term t_0plus1=tf.createFunctionTerm(func_plus1,
						new Term[]{t_0});

	// help rule r1: find(rn) replacewith(0) replacewith(0)
	RewriteTacletBuilder rwb1=new RewriteTacletBuilder();	
	rwb1.setName(new Name("r1"));
	rwb1.setFind(t_rn);
	rwb1.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,
				    t_0));

	

	//pred-succ-elim-rule
	// find(rn -1 +1) replacewith(rn) replacewith(0 +1) addrule(r1)
	RewriteTacletBuilder rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(t_rnminus1plus1);
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,
				    t_rn));
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST
				    .prepend(rwb1.getTaclet()),
				    t_0plus1));
	rwbuilder.setName(new Name("pred-succ-elim"));
       	pluszeroelim=rwbuilder.getRewriteTaclet();	

	//plus-zero-elim
	// find(rn + 0) replacewith(rn)
	rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(tf.createFunctionTerm(func_plus,
						new Term[]{t_rn, t_0}));
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,
				    t_rn));
	rwbuilder.setName(new Name("plus-zero-elim"));
       	predsuccelim=rwbuilder.getRewriteTaclet();

	//zero-plus-elim
	// find(0 + rn) replacewith(rn)
	rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(tf.createFunctionTerm(func_plus,
						new Term[]{t_0, t_rn}));
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,
				    t_rn));
	rwbuilder.setName(new Name("zero-plus-elim"));
       	zeropluselim=rwbuilder.getRewriteTaclet();


	//closewitheq
	// find(=> rn=rn)
	SuccTacletBuilder sbuilder=new SuccTacletBuilder();
	Term t_rneqrn=tf.createFunctionTerm(func_eq,
					    new Term[]{t_rn, t_rn});
	sbuilder.setFind( t_rneqrn);
	sbuilder.setName(new Name("close-with-eq"));
       	closewitheq=sbuilder.getSuccTaclet();


	//switch first succ
	// find((rn +1) + rm) replacewith((rn + rm) +1)
	Term t_rnplus1=tf.createFunctionTerm(func_plus1, 
					   new Term[]{t_rn});
	Term t_rnplus1plusrm=tf.createFunctionTerm(func_plus, 
					   new Term[]{t_rnplus1, t_rm});

	Term t_rnplusrm=tf.createFunctionTerm(func_plus, 
					   new Term[]{t_rn, t_rm});
	Term t_rnplusrmplus1=tf.createFunctionTerm(func_plus1, 
					   new Term[]{t_rnplusrm});

	rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(t_rnplus1plusrm);
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,
				    t_rnplusrmplus1));
	rwbuilder.setName(new Name("switch-first-succ"));
       	switchfirstsucc=rwbuilder.getRewriteTaclet();
	


	//switch second succ
	// find(rn + (rm +1)) replacewith((rn + rm) +1)
	Term t_rmplus1=tf.createFunctionTerm(func_plus1, 
					   new Term[]{t_rm});
	Term t_rnplus_rmplus1=tf.createFunctionTerm(func_plus, 
					   new Term[]{t_rn, t_rmplus1});
	rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(t_rnplus_rmplus1);
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,
				    t_rnplusrmplus1));
	rwbuilder.setName(new Name("switch-second-succ"));
       	switchsecondsucc=rwbuilder.getRewriteTaclet();

	//elim-succ
	// find(rn +1 = rm +1) replacewith(rn=rm)
	Term t_rneqrm=tf.createFunctionTerm(func_eq,
					    new Term[]{t_rn, t_rm});
	rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(tf.createFunctionTerm(func_eq,
						new Term[]{t_rnplus1,
							   t_rmplus1}));
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,
				    t_rneqrm));
	rwbuilder.setName(new Name("succ-elim"));
       	succelim=rwbuilder.getRewriteTaclet();

    }

    public void setUp() {
	nss = new NamespaceSet();

	parseDecls("\\sorts { Nat; testSort1; }\n"+
		   "\\schemaVariables {\n"+
		   "  \\formula b,b0;\n" +
		   "  \\term testSort1 x;\n" +
		   "  \\variables testSort1 z;\n" +
		   "}\n"
		   );

	sort1 = (Sort)nss.sorts().lookup(new Name("testSort1"));
	nat = (Sort)nss.sorts().lookup(new Name("Nat"));

	b = (SchemaVariable)nss.variables().lookup(new Name("b"));

	// createTaclets
	createTaclets();
	createNatTaclets();
	
	// problem

	String test1="\\predicates {A; B; } (A -> B) -> (!(!(A -> B)))";
	Term t_test1=null;
	try{
	    StringReader fr = new StringReader(test1);
	    KeYParser parser=
		new KeYParser(ParserMode.PROBLEM,new KeYLexer(fr,null));
	    t_test1=parser.problem();
	} catch (Exception e) {
	    System.err.println("Parser Error or Input Error");
	    fail("Parser Error");
	}	
	ConstrainedFormula cf=new ConstrainedFormula(t_test1, 
						   Constraint.BOTTOM);
	ConstrainedFormula cf2=new ConstrainedFormula(t_test1, 
						    Constraint.BOTTOM);
	seq_test1 = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,
		    Semisequent.EMPTY_SEMISEQUENT.insert(0,cf).semisequent()); 
	seq_test2 = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT
					  .insert(0,cf).semisequent(), 
					  Semisequent.EMPTY_SEMISEQUENT); 
	seq_test3 =
	    Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,cf).semisequent(),
			       Semisequent.EMPTY_SEMISEQUENT.insert(0,cf2).semisequent()); 
	
	
	func_p=new RigidFunction(new Name("P"),Sort.FORMULA,
				new Sort[]{sort1});
	nss.functions().add(func_p);

	//nat problem:
	Function const_c=new RigidFunction(new Name("c"),nat,new PrimitiveSort[0]);
	nss.functions().add(const_c);
	Function const_d=new RigidFunction(new Name("d"),nat,new PrimitiveSort[0]);
	nss.functions().add(const_d);

	Term t_c=tf.createFunctionTerm(const_c,new Term[]{});
	Term t_d=tf.createFunctionTerm(const_d,new Term[]{});
	Term t_cplusd=tf.createFunctionTerm(func_plus,new Term[]{t_c,t_d});	
	Term t_dminus1=tf.createFunctionTerm(func_min1,new Term[]{t_d});
	Term t_dminus1plus1=tf.createFunctionTerm(func_plus1,
						  new Term[]{t_dminus1});	
	Term t_dminus1plus1plusc=tf.createFunctionTerm
	    (func_plus,new Term[]{t_dminus1plus1,t_c});
	Term t_eq1=tf.createFunctionTerm
	    (func_eq,new Term[]{t_cplusd, t_dminus1plus1plusc});
	

	Term t_cplus1=tf.createFunctionTerm(func_plus1,new Term[]{t_c});
	Term t_cplus1plusd=tf.createFunctionTerm(func_plus,
						 new Term[]{t_cplus1,
							    t_d});
	Term t_dpluscplus1=tf.createFunctionTerm(func_plus,
						 new Term[]{t_d,t_cplus1});
	Term t_eq2=tf.createFunctionTerm
	    (func_eq,new Term[]{ t_cplus1plusd, t_dpluscplus1});
	Term tnat=tf.createJunctorTerm(Op.IMP, t_eq1, t_eq2);

	// => (c+d) = ((d -1 +1) +c) -> (c +1)+d = (d+c) +1
	seq_testNat=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT,
	     Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new ConstrainedFormula(tnat, Constraint.BOTTOM)).semisequent());


	z = new LogicVariable(new Name("z"),sort1);
       	Term t_z=tf.createFunctionTerm(z,new Term[0]);
	Term t_allzpz=tf.createQuantifierTerm(Op.ALL,new
	    LogicVariable[]{z}, tf.createFunctionTerm(func_p,new Term[]{t_z}));
 	ConstrainedFormula cf3=new ConstrainedFormula(t_allzpz, 
						    Constraint.BOTTOM);
 	seq_testAll=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, 
 					  Semisequent.EMPTY_SEMISEQUENT
					  .insert(0,cf3).semisequent()); 
	


    }
    
    private KeYParser stringDeclParser(String s) {
	return new KeYParser(ParserMode.DECLARATION, new KeYLexer(new StringReader(s),null),
			      "No file. CreateTacletForTests.stringParser("+s+")",
			      services, nss);
    }

    public void parseDecls(String s) {
	try {
	    KeYParser p = stringDeclParser(s);
	    p.decls();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }
     
    private KeYParser stringTacletParser(String s) {
	return new KeYParser(ParserMode.TACLET, new KeYLexer(new StringReader(s),null),
			      "No file. CreateTacletForTests.stringParser("+s+")",
			      tf, services, nss);
    }
    
    Taclet parseTaclet(String s) {
   	try {
	    KeYParser p = stringTacletParser(s);
	    
	    return p.taclet(SetAsListOfChoice.EMPTY_SET);
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

}
