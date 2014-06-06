// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/** these tests are used to control if the collision mechanisms work
 * correct. Collisions may be: collisions between variablesv, with the
 * context or or inside formula- and termsvs
 */
package de.uka.ilkd.key.rule;

import junit.framework.TestCase;
import de.uka.ilkd.key.gui.TacletInstantiationsTableModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.SVInstantiationException;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class TestCollisionResolving extends TestCase {

    Sort s;
    Goal goal;
    Services services;

    public TestCollisionResolving(String name) {
	super(name);
    }

    @Override
    public void setUp() {
	TacletForTests.setStandardFile(TacletForTests.testRules);
	TacletForTests.parse();
	s = (Sort)TacletForTests.getSorts().lookup(new Name("s"));

   	services = TacletForTests.services();

	//build a goal (needed for creating TacletInstantiationsTableModel)
    	Proof proof = new Proof(services);
       	Semisequent empty = Semisequent.EMPTY_SEMISEQUENT;
    	Sequent seq = Sequent.createSequent(empty, empty);
	
	Node node = new Node(proof, seq);
	TacletIndex tacletIndex = new TacletIndex();
	BuiltInRuleAppIndex builtInRuleAppIndex = new BuiltInRuleAppIndex(null);
	RuleAppIndex ruleAppIndex = new RuleAppIndex(tacletIndex,
						     builtInRuleAppIndex, proof.getServices());
	goal = new Goal(node, ruleAppIndex);
    }

    @Override
    public void tearDown() {
        s = null;
        goal = null;
        services = null;
    }
    
    public void testCollisionResolvingOfSchemaVariable() {
	// the term has to be built manually because we have to ensure
	// object equality of the LogicVariable x
	LogicVariable x = new LogicVariable(new Name("x"), s);
	Function p = new Function(new Name("p"), Sort.FORMULA, new Sort[]{s});
	Function q = new Function(new Name("q"), Sort.FORMULA, new Sort[]{s});

	Term t_x = services.getTermFactory().createTerm(x);	
	Term t_p_x = services.getTermFactory().createTerm(p, new Term[]{t_x}, null, null);
	Term t_q_x = services.getTermFactory().createTerm(q, new Term[]{t_x}, null, null);
   TermBuilder tb = services.getTermBuilder();
	Term t_all_p_x =
	    tb.all(x, t_p_x);
	Term t_ex_q_x =
	    tb.ex(x, t_q_x);
	Term term = 
	        services.getTermFactory().createTerm(Junctor.AND, t_all_p_x,
						  t_ex_q_x);
	FindTaclet coll_varSV = (FindTaclet) TacletForTests.getTaclet
	    ("TestCollisionResolving_coll_varSV").taclet();

	TacletApp result = NoPosTacletApp.createNoPosTacletApp
	    (coll_varSV, coll_varSV.match
	     (term, 
	      coll_varSV.find(),
	      MatchConditions.EMPTY_MATCHCONDITIONS,
	      services),
	      services);

	SchemaVariable b 
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("b"));
	SchemaVariable c 
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("c"));
	SchemaVariable u
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("u"));
	SchemaVariable v
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("v"));

	SVInstantiations insts=result.instantiations();
	assertTrue("Same object for different conceptual variables",
		   ((Term)insts.getInstantiation(b)).sub(0).op() !=
		   ((Term)insts.getInstantiation(c)).sub(0).op());
	assertSame(((Term)insts.getInstantiation(u)).op(),
		   ((Term)insts.getInstantiation(b)).sub(0).op());
	assertSame(((Term)insts.getInstantiation(v)).op(),
		   ((Term)insts.getInstantiation(c)).sub(0).op());
    }
    
    public void testCollisionResolvingWithContext() {
	// the term has to be built manually because we have to ensure
	// object equality of the LogicVariable x
	LogicVariable x = new LogicVariable(new Name("x"), s);
	Function p = new Function(new Name("p"), Sort.FORMULA, new Sort[]{s});
	Function q = new Function(new Name("q"), Sort.FORMULA, new Sort[]{s});

	TermBuilder tb = services.getTermBuilder();

	final TermFactory tf = services.getTermFactory();
    
	Term t_x = tf.createTerm(x);	
	Term t_p_x = tf.createTerm(p, new Term[]{t_x}, null, null);
	Term t_q_x = tf.createTerm(q, new Term[]{t_x}, null, null);
	

	Term t_ex_q_x =
	    tb.ex(x, t_q_x);

	Term t_px_and_exxqx = 
	    tf.createTerm(Junctor.AND, t_p_x,
						  t_ex_q_x);
	Term term =
	    tb.all(x, t_px_and_exxqx);

	FindTaclet coll_varSV = (FindTaclet) TacletForTests.getTaclet
	    ("TestCollisionResolving_coll_context").taclet();

	PosInOccurrence pos=new PosInOccurrence(new SequentFormula(term),
						PosInTerm.getTopLevel().down(0),
						true);

	TacletApp result 
	    = PosTacletApp.createPosTacletApp(coll_varSV, coll_varSV.match
					      (term.sub(0), 
					       coll_varSV.find(),
					       MatchConditions.EMPTY_MATCHCONDITIONS,
					       services),pos, services);

	SchemaVariable b 
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("b"));
	SchemaVariable c
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("c"));
	SchemaVariable u
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("u"));

	SVInstantiations insts=result.instantiations();
	assertTrue("Same object for different conceptual variables",
		   ((Term)insts.getInstantiation(b)).sub(0).op() !=
		   ((Term)insts.getInstantiation(c)).sub(0).op());
	assertSame(((Term)insts.getInstantiation(u)).op(),
		   ((Term)insts.getInstantiation(c)).sub(0).op());
    }
    
    public void testVarNamespaceCreationWithContext() {
	Term term = TacletForTests.parseTerm("\\forall s x; p(x)");
		
	FindTaclet taclet = (FindTaclet) TacletForTests.getTaclet
	    ("TestCollisionResolving_ns1").taclet();
	PosInOccurrence pos=new PosInOccurrence(new SequentFormula(term),
						PosInTerm.getTopLevel().down(0),
						true);
	TacletApp app 
	    = PosTacletApp.createPosTacletApp(taclet, 
					      taclet.match(term.sub(0), taclet.find(),
							   MatchConditions.EMPTY_MATCHCONDITIONS,
							   null),
			                      pos,
			                      services);
	TacletApp app1=app.prepareUserInstantiation(services);
	assertSame(app, app1);
	TacletInstantiationsTableModel instModel
	    = new TacletInstantiationsTableModel(app, TacletForTests.services(),
						 TacletForTests.getNamespaces(),
						 TacletForTests.getAbbrevs(),
						 goal);

	boolean exceptionthrown = false;
	try {
	    app=instModel.createTacletAppFromVarInsts();
	} catch (IllegalStateException e){
	    exceptionthrown=true;
	} catch (SVInstantiationException ipe){
	    exceptionthrown=true;
	}
	assertTrue("Calling the creation of TacletApps before Input should "
		   +"throw exception", exceptionthrown);

	instModel.setValueAt("x",1,1);

	try {
	    app=instModel.createTacletAppFromVarInsts();
	} catch (Exception e) {
	    fail("The exception "+e+ "has not been expected.");
	}

	assertNotNull(app);
    }
    
    public void testVarNamespaceCreationWithPrefix() {
        TacletApp app = TacletForTests.getTaclet
        ("TestCollisionResolving_ns2");
        TacletApp app1=app.prepareUserInstantiation(services);
        assertSame(app, app1);

        TacletInstantiationsTableModel instModel
        = new TacletInstantiationsTableModel(app, services,
                TacletForTests.getNamespaces(),
                TacletForTests.getAbbrevs(),
                goal);
        boolean exceptionthrown=false;
        try {
            app=instModel.createTacletAppFromVarInsts();
        } catch (IllegalStateException e){
            exceptionthrown=true;
        }  catch (SVInstantiationException ipe){
            exceptionthrown=true;
        }
        assertTrue("Calling the creation of TacletApps before Input should "
                +"throw exception", exceptionthrown);
        SchemaVariable u
        = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("u"));	       
        if (instModel.getValueAt(0,0)==u) {
            instModel.setValueAt("x",0,1);
            instModel.setValueAt("f(x)",1,1);
        } else {
            instModel.setValueAt("f(x)",0,1);
            instModel.setValueAt("x",1,1);
        }
        try {
            app=instModel.createTacletAppFromVarInsts();
        } catch (Exception e) {
            fail("The exception "+e+ "has not been expected.");
        }
        assertNotNull(app);

    }

     public void testNameConflict1() {
         Services services = new Services(AbstractProfile.getDefaultProfile());
         SchemaVariable u
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("u"));	
	SchemaVariable v
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("v"));	
	FindTaclet taclet = (FindTaclet) TacletForTests.getTaclet
	    ("TestCollisionResolving_name_conflict").taclet();
	Semisequent semiseq
	    = Semisequent.EMPTY_SEMISEQUENT
	    .insert(0, new SequentFormula(TacletForTests.parseTerm
					      ("\\forall s x; p(x)"))).semisequent()
	    .insert(1, new SequentFormula(TacletForTests.parseTerm
					      ("\\exists s x; p(x)"))).semisequent();
	Sequent seq=Sequent.createSuccSequent(semiseq);
	PosInOccurrence pos=new PosInOccurrence(semiseq.get(0),
						PosInTerm.getTopLevel(), false);

	NoPosTacletApp app0 = NoPosTacletApp.createNoPosTacletApp ( taclet );
	app0 = app0.matchFind ( pos,
				       services);
	app0 = (NoPosTacletApp)app0.findIfFormulaInstantiations 
	( seq, services ).head ();
	TacletApp app = app0.setPosInOccurrence ( pos, services );
	/*
	IList<SVInstantiations> sviList=taclet.matchIf
	    (seq, taclet.match(semiseq.get(0).formula(), taclet.find(),
			       MatchConditions.EMPTY_MATCHCONDITIONS,
			       null, Constraint.BOTTOM), null);
	TacletApp app 
	    = PosTacletApp.createPosTacletApp(taclet, sviList.head(), pos);
	*/
	TacletApp app1=app.prepareUserInstantiation(services);
	assertTrue("A different TacletApp should have been created to resolve"
		   +" name conflicts", app!=app1);
	
	assertTrue("The names of the instantiations of u and v should be different",
		   !(((Term)app1.instantiations().getInstantiation(u)).op().name().equals
		     (((Term)app1.instantiations().getInstantiation(v)).op().name())));
    }

    public void testNameConflictAfterInput() {

	TacletApp app = TacletForTests.getTaclet
	    ("TestCollisionResolving_name_conflict2");
	TacletApp app1=app.prepareUserInstantiation(services);
	assertSame(app, app1);

	TacletInstantiationsTableModel instModel
	    = new TacletInstantiationsTableModel(app, services,
						 TacletForTests.getNamespaces(),
						 TacletForTests.getAbbrevs(),
						 goal);
	boolean exceptionthrown=false;
	try {
	    app=instModel.createTacletAppFromVarInsts();
	} catch (IllegalStateException e){
	    exceptionthrown=true;
	}  catch (SVInstantiationException ipe){
	    exceptionthrown=true;
	}
	assertTrue("Calling the creation of TacletApps before Input should "
		   +"throw exception", exceptionthrown);
	SchemaVariable u
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("u"));	
	SchemaVariable v
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("v"));	
	SchemaVariable w0 = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("w0"));
	for (int i=0; i<3; i++) {
	    if (instModel.getValueAt(i,0)==u) {
		instModel.setValueAt("x",i,1);		
	    }
	    if (instModel.getValueAt(i,0)==v) {
		instModel.setValueAt("x",i,1);		
	    }
	    if (instModel.getValueAt(i,0)==w0) {
		instModel.setValueAt("f(x)",i,1);		
	    }
	} 
	exceptionthrown=false;
	try {
	    app=instModel.createTacletAppFromVarInsts();
	} catch (IllegalStateException e){
	    exceptionthrown=true;
	}  catch (SVInstantiationException ipe){
	    exceptionthrown=true;
	}
	assertTrue("As names of instantiations of VarSVs u and v in prefix of w0"
		   +"are equal, an exception should be thrown.", exceptionthrown);
	// next attempt
	for (int i=0; i<3; i++) {
	    if (instModel.getValueAt(i,0)==u) {
		instModel.setValueAt("y",i,1);		
	    }
	    if (instModel.getValueAt(i,0)==v) {
		instModel.setValueAt("x",i,1);		
	    }
	    if (instModel.getValueAt(i,0)==w0) {
		instModel.setValueAt("f(x)",i,1);		
	    }
	} 
	try {
	    app = instModel.createTacletAppFromVarInsts();
	} catch (Exception e) {
            fail("The exception "+e+ "has not been expected.");
	}

	assertNotNull("Correct instantiation input should be honored!",app);	
    }

/* COMMENTED OUT! It has to be checked if the instantiation checking is to restrictive.
    public void testNameConflictWithContext() {

	SchemaVariable v
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("v"));	
	FindTaclet taclet = (FindTaclet) TacletForTests.getTaclet
	    ("TestCollisionResolving_name_conflict_with_context").taclet();
	Semisequent semiseq
	    = Semisequent.EMPTY_SEMISEQUENT
	    .insert(0, new SequentFormula(TacletForTests.parseTerm("ex x:s"
								    +".p(x)")))
	    .insert(1, new SequentFormula(TacletForTests.parseTerm("all x:s"
								    +".p(x)")));
	Sequent seq=Sequent.createSuccSequent(semiseq);
	PosInOccurrence pos=new PosInOccurrence(semiseq.get(1),
						PosInTerm.TOP_LEVEL.down(0),
						seq);
	IList<SVInstantiations> sviList=taclet.matchIf
	    (seq, taclet.match(semiseq.get(1).formula().sub(0), taclet.find(),
			     taclet.createInitialInstantiation()));
	TacletApp app 
	    = PosTacletApp.createPosTacletApp(taclet, sviList.head(), pos);
	TacletApp app1=app.prepareUserInstantiation();
	assertTue("A different TacletApp should have been created to resolve"
	          +" name conflicts", app!=app1);
	assertTrue("The names of x and the instantiations of v should be different",
	           !(new Name("x")).equals
	           (((Term)app1.instantiations().getInstantiation(v)).op().name()));

    }

*/    

    public void testNameConflictWithContextAfterInput() {

	FindTaclet taclet = (FindTaclet) TacletForTests.getTaclet
	    ("TestCollisionResolving_name_conflict_with_context2").taclet();
	Term term=TacletForTests.parseTerm("\\forall s x; p(x)");
	PosInOccurrence pos=new PosInOccurrence(new SequentFormula(term),
						PosInTerm.getTopLevel().down(0),
						true);
	MatchConditions mc=taclet.match(term.sub(0), taclet.find(),
					MatchConditions.EMPTY_MATCHCONDITIONS,
					null);
	TacletApp app 
	    = PosTacletApp.createPosTacletApp(taclet, mc, pos, services);
	TacletApp app1=app.prepareUserInstantiation(services);
	assertSame("Actually there are no conflicts yet.", app, app1);
	TacletInstantiationsTableModel instModel
	    = new TacletInstantiationsTableModel(app, services,
						 TacletForTests.getNamespaces(),
						 TacletForTests.getAbbrevs(),
						 goal);
	boolean exceptionthrown=false;
	try {
	    app=instModel.createTacletAppFromVarInsts();
	} catch (IllegalStateException e){
	    exceptionthrown=true;
	}  catch (SVInstantiationException ipe){
	    exceptionthrown=true;
	}
	assertTrue("Calling the creation of TacletApps before Input should "
		   +"throw exception", exceptionthrown);
	SchemaVariable v
	    = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("v"));	
	SchemaVariable w0 = (SchemaVariable) TacletForTests.getVariables().lookup(new Name("w0"));
	for (int i=1; i<3; i++) {
	    if (instModel.getValueAt(i,0)==v) {
		instModel.setValueAt("x",i,1);		
	    }
	    if (instModel.getValueAt(i,0)==w0) {
		instModel.setValueAt("f(x)",i,1);		
	    }
	} 
	exceptionthrown=false;
	try {
	    app=instModel.createTacletAppFromVarInsts();
	} catch (IllegalStateException e){
	    exceptionthrown=true;
	}  catch (SVInstantiationException ipe){
	    exceptionthrown=true;
	}
	assertTrue("As names of x and instantiations of VarSV v in prefix of w0"
		   +"are equal, an exception should be thrown.", exceptionthrown);
	// next attempt
	for (int i=1; i<3; i++) {
	    if (instModel.getValueAt(i,0)==v) {
		instModel.setValueAt("y",i,1);		
	    }
	    if (instModel.getValueAt(i,0)==w0) {
		instModel.setValueAt("f(x)",i,1);		
	    }
	} 
	try {
	    app=instModel.createTacletAppFromVarInsts();
	} catch (Exception e) {
            fail("The exception "+e+ "has not been expected.");
	}
	assertNotNull("Correct instantiation input should be honored!",app);	

    }

}