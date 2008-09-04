// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;
import java.io.StringReader;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.*;

public class TestTacletPopup {

    static AntecTaclet impleft;
    static SuccTaclet impright;
    static AntecTaclet notleft;
    static SuccTaclet notright;
    static SuccTaclet close;
    static SuccTaclet allright;
    static AntecTaclet allleft;
    static AntecTaclet remove_or_left;
    static SuccTaclet remove_or_right;
    static AntecTaclet remove_and_left;
    static SuccTaclet remove_and_right;
    static RewriteTaclet contradiction;
    static Taclet cut;
    static RewriteTaclet predsuccelim;
    static RewriteTaclet pluszeroelim;
    static RewriteTaclet zeropluselim;
    static RewriteTaclet succelim;
    static RewriteTaclet switchsecondsucc;
    static RewriteTaclet switchfirstsucc;
    static SuccTaclet closewitheq;


    static Sequent seq_test1;
    static Sequent seq_test2;
    static Sequent seq_test3;
    static Sequent seq_testAll;
    static Sequent seq_testNat;

    static SchemaVariable b;
    static SchemaVariable x;
    static SchemaVariable x0;
    static SchemaVariable t0;
    static LogicVariable z;

    static Sort nat = new PrimitiveSort(new Name("Nat"));

    static TermFactory tf=TermFactory.DEFAULT;

    public static Namespace var_ns=new Namespace();
    public static Namespace func_ns=new Namespace();
    public static Namespace sort_ns=new Namespace();

    private TestTacletPopup() {}	

    static {
	sort_ns.add(Sort.FORMULA);	
	sort_ns.add(nat);
	
	// imp-left rule
	// find(b->b0 =>) replacewith(b0 =>) replacewith(=> b) 
	AntecTacletBuilder impleftbuilder=new AntecTacletBuilder();
	b=SchemaVariableFactory.createFormulaSV(new Name("b"), false);
	SchemaVariable b0 = SchemaVariableFactory.createFormulaSV(new Name("b0"), false);
	Term t_b=tf.createFunctionTerm((SortedSchemaVariable)b,new Term[0]);
	Term t_b0=tf.createFunctionTerm((SortedSchemaVariable)b0,new Term[0]);
	Term t_bimpb0=tf.createJunctorTerm(Op.IMP,new Term[]{t_b, t_b0});
	Term t_bandb0 = tf.createJunctorTerm(Op.AND, t_b, t_b0);
	Term t_borb0 = tf.createJunctorTerm(Op.OR, t_b, t_b0);

	impleftbuilder.setFind(t_bimpb0);
	impleftbuilder.setName(new Name("imp-left"));
	Sequent ante = Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new ConstrainedFormula
		 (t_b0, Constraint.BOTTOM)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT); 
	impleftbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,
				      ante));
	Sequent succ=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,
		    Semisequent.EMPTY_SEMISEQUENT.insert(0, new
			ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent()); 
	impleftbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,
				      succ));
	impleft=impleftbuilder.getAntecTaclet();

	// imp-right rule
	// find(=> b->b0) replacewith(b => b0) 
	SuccTacletBuilder imprightbuilder=new SuccTacletBuilder();
	imprightbuilder.setFind(t_bimpb0);
	Sequent seq=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0,new
		ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT.insert(0, new
		 ConstrainedFormula(t_b0, Constraint.BOTTOM)).semisequent()); 
	imprightbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,
				      seq));
	imprightbuilder.setName(new Name("imp-right"));
	impright=imprightbuilder.getSuccTaclet();

	// not-left rule
	// find(not b=>) replacewith(=>b)
	Term t_notb=tf.createJunctorTerm(Op.NOT, new Term[]{t_b});
	AntecTacletBuilder notleftbuilder=new AntecTacletBuilder();
	notleftbuilder.setFind(t_notb);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,
		    Semisequent.EMPTY_SEMISEQUENT.insert(0, new
			ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent()); 
	notleftbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,
				      seq));	
	notleftbuilder.setName(new Name("not-left"));
	notleft=notleftbuilder.getAntecTaclet();

	// not-right rule
	// find(=>not b) replacewith(b=>)
	SuccTacletBuilder notrightbuilder=new SuccTacletBuilder();
	notrightbuilder.setFind(t_notb);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
			ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent(),
		    Semisequent.EMPTY_SEMISEQUENT); 
	notrightbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,
				      seq));
	notrightbuilder.setName(new Name("not-right"));
       	notright=notrightbuilder.getSuccTaclet();

	// cut rule
	// add(b=>) add(=>b)
	NoFindTacletBuilder nfbuilder=new NoFindTacletBuilder();
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
			ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent(),
		    Semisequent.EMPTY_SEMISEQUENT); 
	nfbuilder.addTacletGoalTemplate(new
	    TacletGoalTemplate(seq, SLListOfTaclet.EMPTY_LIST));

	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,
		    Semisequent.EMPTY_SEMISEQUENT.insert(0,new
			ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent());
		     
	nfbuilder.addTacletGoalTemplate(new
	    TacletGoalTemplate(seq, SLListOfTaclet.EMPTY_LIST));
	nfbuilder.setName(new Name("cut rule"));

       	cut=nfbuilder.getNoFindTaclet();


	ListOfTaclet emptyTacletList=SLListOfTaclet.EMPTY_LIST;
	
	// close rule
	// if (b=>) find(=>b) 
	SuccTacletBuilder closebuilder=new SuccTacletBuilder();
	closebuilder.setFind(t_b);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
			ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent(),
		    Semisequent.EMPTY_SEMISEQUENT); 
	closebuilder.setIfSequent(seq);
	closebuilder.setName(new Name("close"));
       	close=closebuilder.getSuccTaclet();


	// contradiction rule
	// find(b->b0) replacewith(-b0 -> -b)
	Term t_notb0=tf.createJunctorTerm(Op.NOT, new Term[]{t_b0});
	Term t_notb0impnotb=tf.createJunctorTerm(Op.IMP,new Term[]{t_notb0, t_notb});

	RewriteTacletBuilder rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(t_bimpb0);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
			ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent(),
		    Semisequent.EMPTY_SEMISEQUENT); 
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    emptyTacletList,
				    t_notb0impnotb));
	rwbuilder.setName(new Name("contradiction rule"));
       	contradiction=rwbuilder.getRewriteTaclet();

	// all-right
	// find (=>Vx:b) add(=>b[x/t0])
	SuccTacletBuilder allrightbuilder=new SuccTacletBuilder();
	x = SchemaVariableFactory.createVariableSV(new Name("x"),nat, false);
	t0 = SchemaVariableFactory.createTermSV(new Name("t0"),nat, false);
	Term t_t0=tf.createFunctionTerm((SortedSchemaVariable)t0,new Term[0]);
	Term t_allxb=tf.createQuantifierTerm(Op.ALL,
					     new SortedSchemaVariable[]{(SortedSchemaVariable)x},t_b);
	Term t_subxt0b=tf.createSubstitutionTerm(Op.SUBST,(SortedSchemaVariable)x,t_t0,t_b);
	allrightbuilder.setFind(t_allxb);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,
		    Semisequent.EMPTY_SEMISEQUENT.insert(0,new
			ConstrainedFormula(t_subxt0b, Constraint.BOTTOM)).semisequent());

	allrightbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(seq,
				      SLListOfTaclet.EMPTY_LIST,				      
				      Sequent.EMPTY_SEQUENT));
	allrightbuilder.setName(new Name("all-right"));
       	allright=allrightbuilder.getSuccTaclet();


	// all-left
	// find (Vx:b=>) add (b[x/t0]=>)
	AntecTacletBuilder allleftbuilder=new AntecTacletBuilder();
	allleftbuilder.setFind(t_allxb);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
	    ConstrainedFormula(t_subxt0b, Constraint.BOTTOM)).semisequent(),
				  Semisequent.EMPTY_SEMISEQUENT);

	allleftbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(seq,
				      SLListOfTaclet.EMPTY_LIST,				      
				      Sequent.EMPTY_SEQUENT));
	allleftbuilder.setName(new Name("all-left"));
       	allleft=allleftbuilder.getAntecTaclet();

	// remove-and-left
	// find (b & c=>) replacewith (b, c=>)
	AntecTacletBuilder remove_and_leftbuilder=new AntecTacletBuilder();

	remove_and_leftbuilder.setFind(t_bandb0);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
	    ConstrainedFormula
	    (t_b0, Constraint.BOTTOM)).semisequent().insert(0,new
		ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent(),
				  Semisequent.EMPTY_SEMISEQUENT);

	remove_and_leftbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,				      
				      seq));
	remove_and_leftbuilder.setName(new Name("remove-and-left"));
       	remove_and_left=remove_and_leftbuilder.getAntecTaclet();

	// remove-or-left
	// find (b | c=>) replacewith (b =>); replacewith(c => )
	AntecTacletBuilder remove_or_leftbuilder=new AntecTacletBuilder();
	remove_or_leftbuilder.setFind(t_borb0);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
	    ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent(),
				  Semisequent.EMPTY_SEMISEQUENT);

	remove_or_leftbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,
				      seq));

	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,new
	    ConstrainedFormula(t_b0, Constraint.BOTTOM)).semisequent(), 
				  Semisequent.EMPTY_SEMISEQUENT);

	remove_or_leftbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,				      
				      seq));

	remove_or_leftbuilder.setName(new Name("remove-or-left"));
       	remove_or_left=remove_or_leftbuilder.getAntecTaclet();

	// remove-and-right
	// find (=> b & c) replacewith (=> b); replacewith(=>c)
	SuccTacletBuilder remove_and_rightbuilder=new SuccTacletBuilder();
	remove_and_rightbuilder.setFind(t_bandb0);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, 
				  Semisequent.EMPTY_SEMISEQUENT.insert
				  (0, new ConstrainedFormula
				      (t_b, Constraint.BOTTOM)).semisequent());

	remove_and_rightbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,				      
				      seq));

	seq=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT, 
	     Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new ConstrainedFormula(t_b0, Constraint.BOTTOM)).semisequent());

	remove_and_rightbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,				      
				      seq));

	remove_and_rightbuilder.setName(new Name("remove-and-right"));
       	remove_and_right=remove_and_rightbuilder.getSuccTaclet();


	// remove-or-right
	// find (=> b or c) replacewith (=>b, c)
	SuccTacletBuilder remove_or_rightbuilder=new SuccTacletBuilder();
	remove_or_rightbuilder.setFind(t_borb0);
	seq=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, 
				  Semisequent.EMPTY_SEMISEQUENT.insert(0,new
	    ConstrainedFormula(t_b0, Constraint.BOTTOM)).semisequent().insert(0,new
		ConstrainedFormula(t_b, Constraint.BOTTOM)).semisequent());


	remove_or_rightbuilder.addTacletGoalTemplate(new
	    AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				      SLListOfTaclet.EMPTY_LIST,				      
				      seq));
	remove_or_rightbuilder.setName(new Name("remove-or-right"));
       	remove_or_right=remove_or_rightbuilder.getSuccTaclet();



	//decls for nat
	Function func_0=new RigidFunction(new Name("zero"),nat,new Sort[]{});
	func_ns.add(func_0);
	Function func_plus=new RigidFunction(new Name("plus"),nat,
					new Sort[]{nat,nat});
	func_ns.add(func_plus);
	Function func_min1=new RigidFunction(new Name("pred"),nat,new Sort[]{nat});
	func_ns.add(func_min1);
	Function func_plus1=new RigidFunction(new Name("succ"),nat,new Sort[]{nat});
	func_ns.add(func_plus1);
	SchemaVariable var_rn=SchemaVariableFactory.createTermSV(new Name("rn"),nat, false);
	SchemaVariable var_rm=SchemaVariableFactory.createTermSV(new Name("rm"),nat, false);

	Term t_rn=tf.createFunctionTerm((SortedSchemaVariable)var_rn,new Term[]{});
	Term t_rm=tf.createFunctionTerm((SortedSchemaVariable)var_rm,new Term[]{});
	Term t_0=tf.createFunctionTerm(func_0,new Term[]{});	
	Term t_rnminus1=tf.createFunctionTerm(func_min1,new Term[]{t_rn});
	Term t_rnminus1plus1=tf.createFunctionTerm(func_plus1,
						   new Term[]{t_rnminus1});
	//	Term t_0minus1=tf.createFunctionTerm(func_min1,
	//		     new Term[]{t_0});
	Term t_0plus1=tf.createFunctionTerm(func_plus1,
						new Term[]{t_0});



	// help rule r1: find(rn) replacewith(0) replacewith(0
	RewriteTacletBuilder rwb1=new RewriteTacletBuilder();	
	rwb1.setName(new Name("r1"));
	rwb1.setFind(t_rn);
	rwb1.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,				    
				    t_0));

	

	//pred-succ-elim-rule
	// find(rn -1 +1) replacewith(rn) replacewith(0 +1) addrule(r1)
	rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(t_rnminus1plus1);
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,				    
				    t_rn));
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    emptyTacletList
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
	Term t_rneqrn=tf.createEqualityTerm(t_rn, t_rn);
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
	Term t_rneqrm=tf.createEqualityTerm(t_rn, t_rm);
	rwbuilder=new RewriteTacletBuilder();
	rwbuilder.setFind(tf.createEqualityTerm(t_rnplus1,
						t_rmplus1));
	rwbuilder.addTacletGoalTemplate(new
	    RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
				    SLListOfTaclet.EMPTY_LIST,				    
				    t_rneqrm));
	rwbuilder.setName(new Name("succ-elim"));
       	succelim=rwbuilder.getRewriteTaclet();

	// problem

	String test1="\\predicates {A; B;} (A -> B) -> (!(!(A -> B)))";
	Term t_test1=null;
	try{
	    StringReader fr = new StringReader(test1);
	    KeYParser parser=
		new KeYParser(ParserMode.PROBLEM, new KeYLexer(fr,null));
	    t_test1=parser.problem();
	} catch (Exception e) {
	    System.err.println("Parser Error or Input Error");
	    System.exit(-1);
	    //fail("Parser Error");
	}	

	ConstrainedFormula cf=new ConstrainedFormula(t_test1, Constraint.BOTTOM);
	ConstrainedFormula cf2=new ConstrainedFormula(t_test1, Constraint.BOTTOM);
	seq_test1=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,
		    Semisequent.EMPTY_SEMISEQUENT.insert(0,cf).semisequent()); 

	seq_test2=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,cf).semisequent(), 
			      Semisequent.EMPTY_SEMISEQUENT); 

	seq_test3=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT.insert(0,cf).semisequent(), 
			      Semisequent.EMPTY_SEMISEQUENT.insert(0,cf2).semisequent()); 
	

	z=new LogicVariable(new Name("z"),nat);
	Function p=new RigidFunction(new Name("P"),Sort.FORMULA,new Sort[]{nat});
	func_ns.add(p);
	Term t_z=tf.createFunctionTerm(z,new Term[0]);
	Term t_allzpz
	    =tf.createQuantifierTerm(Op.ALL,
				     new QuantifiableVariable[]{z}, 
				     tf.createFunctionTerm(p,
							 new Term[]{t_z}));
	ConstrainedFormula cf3=new ConstrainedFormula(t_allzpz, 
						    Constraint.BOTTOM);
	seq_testAll=Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, 
					  Semisequent.EMPTY_SEMISEQUENT
					  .insert(0,cf3).semisequent()); 




	//nat problem:
	Function const_c=new RigidFunction(new Name("c"),nat,new Sort[0]);
	func_ns.add(const_c);
	Function const_d=new RigidFunction(new Name("d"),nat,new Sort[0]);
	func_ns.add(const_d);

	Term t_c=tf.createFunctionTerm(const_c,new Term[]{});
	Term t_d=tf.createFunctionTerm(const_d,new Term[]{});
	Term t_cplusd=tf.createFunctionTerm(func_plus,new Term[]{t_c,t_d});
	Term t_dminus1=tf.createFunctionTerm(func_min1,new Term[]{t_d});
	Term t_dminus1plus1=tf.createFunctionTerm(func_plus1,
						  new Term[]{t_dminus1});	
	Term t_dminus1plus1plusc=tf.createFunctionTerm
	    (func_plus,new Term[]{t_dminus1plus1,t_c});
	Term t_eq1=tf.createEqualityTerm
	    (t_cplusd, t_dminus1plus1plusc);
	

	Term t_cplus1=tf.createFunctionTerm(func_plus1,new Term[]{t_c});
	Term t_cplus1plusd=tf.createFunctionTerm(func_plus,new Term[]{t_cplus1,
								      t_d});
	Term t_dpluscplus1=tf.createFunctionTerm(func_plus,
						 new Term[]{t_d,t_cplus1});
	Term t_eq2=tf.createEqualityTerm
	    (t_cplus1plusd, t_dpluscplus1);
	Term tnat=tf.createJunctorTerm(Op.IMP, t_eq1, t_eq2);

	// => (c+d) = ((d -1 +1) +c) -> (c +1)+d = (d+c) +1
	seq_testNat=Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT,
	     Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new ConstrainedFormula(tnat, Constraint.BOTTOM)).semisequent());


    }

    public static TacletIndex createTacletIndex() {
	TacletIndex index=new TacletIndex();

	index.add(allleft);
	index.add(allright);
	index.add(remove_and_left);
	index.add(remove_and_right);
	index.add(remove_or_right);
	index.add(remove_or_left);

	index.add(cut);
      	index.add(close);
	index.add(impleft);
	index.add(impright);
	index.add(notleft);
	index.add(notright);
	index.add(contradiction);
	index.add(cut);
	index.add(predsuccelim);
	index.add(pluszeroelim);
	index.add(zeropluselim);
	index.add(succelim);
	index.add(switchsecondsucc);
	index.add(switchfirstsucc);
	index.add(closewitheq);

	return index;
    }

}
