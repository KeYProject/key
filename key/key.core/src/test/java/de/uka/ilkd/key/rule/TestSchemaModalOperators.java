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

/**
 * tests if match checks the variable conditions in Taclets. 
 */
package de.uka.ilkd.key.rule;


import junit.framework.TestCase;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.TacletIndexKit;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;



public class TestSchemaModalOperators extends TestCase {

    String[] strs={"i=5", "\\<{ while(i>0) {i--;} }\\> i=0",
		   "i=3", "\\[{ if(i==3) {i++;} else {i--;} }\\] i=3",
                   "i=3", "\\[{ if(i==3) {i++;} else {i--;} }\\] i=3" };
    Proof[] proof;
    Proof   mvProof;
   private TermBuilder TB;
   private Services services;
   
    private static Semisequent parseTermForSemisequent(String t) {
	if ("".equals(t)) { 
	    return Semisequent.EMPTY_SEMISEQUENT;
	}
	SequentFormula cf0
	    = new SequentFormula(TacletForTests.parseTerm(t));
	return Semisequent.EMPTY_SEMISEQUENT.insert(0, cf0).semisequent();
    }

    public void setUp() {
	TacletForTests.setStandardFile(TacletForTests.testRules);
	TacletForTests.parse();
        proof = new Proof[strs.length/2];
        for (int i=0; i<proof.length; i++) {
	    Semisequent antec = parseTermForSemisequent(strs[2*i]);
	    Semisequent succ = parseTermForSemisequent(strs[2*i+1]);
	    Sequent s = Sequent.createSequent(antec, succ);	    
	    proof[i]=new Proof("TestSchemaModalOperators", TacletForTests.initConfig());
	    proof[i].setRoot(new Node(proof[i], s));
	}

        services = TacletForTests.services();
        TB = TacletForTests.services().getTermBuilder();
        
	// proof required to test application with mv
	/*
       TermFactory tf=TermFactory.DEFAULT;

	mvProof = new Proof();

	mvProof.setSimplifier(sus);
	
	Sort s = new PrimitiveSort(new Name("test"));

	Function f = new Function(new Name("f"), s, new Sort[]{s, s});
	Function c = new Function(new Name("c"), s, new Sort[]{});

	Metavariable mv_x = new Metavariable(new Name("X"), s);
	Metavariable mv_y = new Metavariable(new Name("Y"), s);
	Metavariable mv = new Metavariable(new Name("mv"), s);

 	Term t_mv = tf.createFunctionTerm(mv, new Term[]{});
 	Term t_mv_x = tf.createFunctionTerm(mv_x, new Term[]{});
 	Term t_mv_y = tf.createFunctionTerm(mv_y, new Term[]{});
		
 	Term t_c = tf.createFunctionTerm(c, new Term[]{});
 	Term t_f_X_c = tf.createFunctionTerm(f, new Term[]{t_mv_x, t_c});
 	Term t_f_c_X = tf.createFunctionTerm(f, new Term[]{t_c, t_mv_x});

	consMV_f_c_X = Constraint.BOTTOM.unify(t_mv, t_f_c_X);
	consMV_f_X_c = Constraint.BOTTOM.unify(t_mv, t_f_X_c);

	SequentFormula cf1 = 
	    new SequentFormula(TacletForTests.parseTerm("A & B"), consMV_f_c_X);
	SequentFormula cf2 = 
	    new SequentFormula(TacletForTests.parseTerm("!(A | B)"), consMV_f_X_c);

	Sequent seq = Sequent.createSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insertLast(cf1).semisequent(),
	     Semisequent.EMPTY_SEMISEQUENT.insertLast(cf2).semisequent());

	mvProof.setRoot(new Node(mvProof, seq));	
	*/
    }
    
    public void tearDown() {
        proof = null;
    }

    public TestSchemaModalOperators(String name) {
	super(name);
	//	Debug.ENABLE_DEBUG = true;
    }

    public void testSchemaModalities1() {
	//	Debug.ENABLE_DEBUG = true;
	
	RewriteTacletBuilder<RewriteTaclet> rtb = new RewriteTacletBuilder<>();

	SchemaVariable fsv = SchemaVariableFactory.createFormulaSV(new Name("post"), true);
	ImmutableSet<Modality> modalities = DefaultImmutableSet.<Modality>nil();
	modalities = modalities.add(Modality.DIA).add(Modality.BOX);
	SchemaVariable osv = SchemaVariableFactory.createModalOperatorSV(
	      new Name("diabox"), Sort.FORMULA, modalities);
	Term tpost = TB.tf().createTerm(fsv, new Term[0]);

	Term find = TB.tf().createTerm(
	    osv,
	    new Term[]{tpost},
	    null,
            JavaBlock.EMPTY_JAVABLOCK);

	Term replace = TB.tf().createTerm(
	    osv,
	    new Term[]{TB.tt()},
	    null,
            JavaBlock.EMPTY_JAVABLOCK);

	rtb.setName(new Name("test_schema_modal1"));
	rtb.setFind(find); 
	rtb.addTacletGoalTemplate(new                                            
	        RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,                           
                                    ImmutableSLList.<Taclet>nil(),                   
                                    replace));                                 

	RewriteTaclet t = rtb.getRewriteTaclet();

	Term goal = TB.prog(
	    Modality.DIA, 
            JavaBlock.EMPTY_JAVABLOCK,
            TB.ff());
         MatchConditions mc=t.getMatcher().matchFind                                                   
                            (goal,                                                        
                             MatchConditions.EMPTY_MATCHCONDITIONS, services);
	 assertNotNull(mc);
	 assertNotNull(mc.getInstantiations().getInstantiation(osv));
	 assertTrue("Schemamodality " + osv + " has not been instantiated", 
	         mc.getInstantiations().isInstantiated(osv));
	 assertTrue(mc.getInstantiations().getInstantiation(osv) == Modality.DIA);

	 PosInOccurrence pos = new PosInOccurrence(new SequentFormula(goal), PosInTerm.getTopLevel(), true);
	 PosTacletApp tacletApp = PosTacletApp.createPosTacletApp(t, mc, pos, services);
	 Term instReplace = 
	         t.getRewriteResult(null, new TermLabelState(), services, tacletApp).formula();
	 assertNotNull(instReplace);
	 assertTrue(instReplace.op() == Modality.DIA);
    }

    public void testSchemaModalities2() {
	//	Debug.ENABLE_DEBUG = true;
	NoPosTacletApp testmodal1=TacletForTests.getRules().lookup("testSchemaModal1");
	TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
	tacletIndex.add ( testmodal1 );
	Goal goal = createGoal ( proof[0].root(), tacletIndex );
	PosInOccurrence applyPos= new 
			PosInOccurrence(goal.sequent().succedent().getFirst(), 
					PosInTerm.getTopLevel(),
					false);
	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
		    getTacletAppAt(TacletFilter.TRUE, applyPos, null);	
	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
	RuleApp rApp=rApplist.head();
	assertTrue("Rule App should be complete", rApp.complete());
	ImmutableList<Goal> goals=rApp.execute(goal, services);
	assertTrue("There should be 1 goal for testSchemaModal1 taclet, was "+goals.size(), goals.size()==1);	
	Sequent seq=goals.head().sequent();
        Semisequent antec0 = parseTermForSemisequent("\\<{ i--; }\\> i=0");
        Semisequent antec1 = parseTermForSemisequent("i=5");
	Semisequent succ = parseTermForSemisequent("\\<{ i--; while(i>0) {i--;} }\\> i=0");

	assertEquals("Wrong antecedent after testSchemaModal1",
			     seq.antecedent().get(0), antec0.get(0));  
	assertEquals("Wrong antecedent after testSchemaModal1",
			     seq.antecedent().get(1), antec1.get(0));  
       	assertEquals("Wrong succedent after testSchemaModal1",
		             seq.succedent().getFirst(), succ.get(0));  	


	//	Debug.ENABLE_DEBUG = false;

    }

    public void testSchemaModalities3() {
	//	Debug.ENABLE_DEBUG = true;
	NoPosTacletApp testmodal2=TacletForTests.getRules().lookup("testSchemaModal2");
	TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
	tacletIndex.add ( testmodal2 );
	Goal goal = createGoal ( proof[1].root(), tacletIndex );
	PosInOccurrence applyPos= new 
			PosInOccurrence(goal.sequent().succedent().getFirst(), 
					PosInTerm.getTopLevel(),
					false);
	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
		    getTacletAppAt(TacletFilter.TRUE, applyPos, null);	
	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
	RuleApp rApp=rApplist.head();
	assertTrue("Rule App should be complete", rApp.complete());
	ImmutableList<Goal> goals=rApp.execute(goal, TacletForTests.services());
	assertTrue("There should be 1 goal for testSchemaModal2 taclet, was "+goals.size(), goals.size()==1);	
	Sequent seq=goals.head().sequent();
        Semisequent antec0 = parseTermForSemisequent("i=3");
	Semisequent succ = parseTermForSemisequent("\\[{ i++; i--; }\\] i=3");

	assertEquals("Wrong antecedent after testSchemaModal2",
			     seq.antecedent().get(0), antec0.get(0));  
       	assertEquals("Wrong succedent after testSchemaModal2",
		             seq.succedent().getFirst(), succ.get(0));  	

	//	Debug.ENABLE_DEBUG = false;

    }

    public void testSchemaModalities4() {
	//	Debug.ENABLE_DEBUG = true;
	NoPosTacletApp testmodal3=TacletForTests.getRules().lookup("testSchemaModal3");
	TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
	tacletIndex.add ( testmodal3 );
	Goal goal = createGoal ( proof[1].root(), tacletIndex );
	PosInOccurrence applyPos= new 
			PosInOccurrence(goal.sequent().succedent().getFirst(), 
					PosInTerm.getTopLevel(),
					false);
	ImmutableList<TacletApp> rApplist=goal.ruleAppIndex().
		    getTacletAppAt(TacletFilter.TRUE, applyPos, null);	
	assertTrue("Too many or zero rule applications.",rApplist.size()==1);
	RuleApp rApp=rApplist.head();
	assertTrue("Rule App should be complete", rApp.complete());
	ImmutableList<Goal> goals=rApp.execute(goal, TacletForTests.services());
	assertTrue("There should be 3 goals for testSchemaModal3 taclet, was "+goals.size(), goals.size()==3);	
	Sequent seq0=goals.head().sequent();
	goals = goals.tail();
	Sequent seq1=goals.head().sequent();
	goals = goals.tail();
	Sequent seq2=goals.head().sequent();
        Semisequent antec0 = parseTermForSemisequent("i=3");
	Semisequent succ0 = parseTermForSemisequent("\\[{ if(i==3) {i++;} else {i--;} }\\] i=3");
	Semisequent succ1 = parseTermForSemisequent("\\<{ if(i==3) {i++;} else {i--;} }\\> i=3");
	Semisequent succ2 = parseTermForSemisequent("\\[{ if(i==3) {i++;} else {i--;} }\\] i=3");


	assertEquals("Wrong antecedent after testSchemaModal3",
			     seq0.antecedent().get(0), antec0.get(0));  
	assertEquals("Wrong antecedent after testSchemaModal3",
			     seq1.antecedent().get(0), antec0.get(0));  
	assertEquals("Wrong antecedent after testSchemaModal3",
			     seq2.antecedent().get(0), antec0.get(0));  
       	assertEquals("Wrong succedent after testSchemaModal3",
		             seq0.succedent().getFirst(), succ0.get(0));  	
       	assertEquals("Wrong succedent after testSchemaModal3",
		             seq1.succedent().getFirst(), succ1.get(0));  	
       	assertEquals("Wrong succedent after testSchemaModal3",
		             seq2.succedent().getFirst(), succ2.get(0));  	

	//	Debug.ENABLE_DEBUG = false;

    }

    private Goal createGoal ( Node n, TacletIndex tacletIndex ) {
	final BuiltInRuleAppIndex birIndex = new BuiltInRuleAppIndex
	    ( new BuiltInRuleIndex () );
	final RuleAppIndex ruleAppIndex = new RuleAppIndex
	    ( tacletIndex, birIndex, n.proof().getServices() );
	final Goal goal = new Goal ( n, ruleAppIndex );
	return goal;
    }

}