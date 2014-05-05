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

/** tests the TacletIndex class.*/
package de.uka.ilkd.key.proof;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.rulefilter.IHTacletFilter;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletForTests;


public class TestTacletIndex extends TestCase{   

    NoPosTacletApp ruleRewriteNonH1H2; 
    NoPosTacletApp ruleNoFindNonH1H2H3;
    NoPosTacletApp ruleAntecH1;
    NoPosTacletApp ruleSucc;
    NoPosTacletApp ruleMisMatch;
    NoPosTacletApp notfreeconflict;
    
    RuleSet h1;
    RuleSet h2;
    RuleSet h3;

    TacletIndex variante_one;
    

    public TestTacletIndex(String name) {
	super(name);
    }

    private Taclet taclet(String name) {
	return TacletForTests.getTaclet(name).taclet();
    }
    
    public void setUp() {
	TacletForTests.parse(System.getProperty("key.home")+
           java.io.File.separator+"system"+java.io.File.separator+
           "test/de/uka/ilkd/key/proof/ruleForTestTacletIndex.taclet");

	h1 = (RuleSet)TacletForTests.getHeuristics().lookup(new Name("h1"));
	h2 = (RuleSet)TacletForTests.getHeuristics().lookup(new Name("h2"));
	h3 = (RuleSet)TacletForTests.getHeuristics().lookup(new Name("h3"));

	ruleRewriteNonH1H2 = NoPosTacletApp.createNoPosTacletApp(taclet("rewrite_noninteractive_h1_h2"));
	ruleNoFindNonH1H2H3 = NoPosTacletApp.createNoPosTacletApp(taclet("nofind_noninteractive_h1_h2_h3"));
	ruleAntecH1 = NoPosTacletApp.createNoPosTacletApp(taclet("rule_antec_h1"));
	ruleSucc = NoPosTacletApp.createNoPosTacletApp(taclet("rule_succ"));
	ruleMisMatch = NoPosTacletApp.createNoPosTacletApp(taclet ("antec_mismatch"));
	notfreeconflict = NoPosTacletApp.createNoPosTacletApp(taclet("not_free_conflict"));
	

	variante_one = new TacletIndex();
	variante_one.add(ruleRewriteNonH1H2);
	variante_one.add(ruleNoFindNonH1H2H3);
	variante_one.add(ruleAntecH1);
	variante_one.add(ruleSucc);


    }
    
    
    public void tearDown() {
        ruleRewriteNonH1H2 = null; 
        ruleNoFindNonH1H2H3 = null;
        ruleAntecH1 = null;
        ruleSucc = null;
        ruleMisMatch = null;
        notfreeconflict = null;
        
        h1 = null;
        h2 = null;
        h3 = null;

        variante_one = null;
    }


    private boolean isRuleIn(ImmutableList<? extends TacletApp> l, TacletApp rule) {
        for (TacletApp aL : l) {
            if (aL.taclet() == rule.taclet()) return true;
        }
	return false;
    }


    /**
     * test disabled. Since 0.632 "noninteractive" is disabled
     */
    public void disabled_testNonInteractiveIsShownOnlyIfHeuristicIsMissed() {
	Term term_p1 = TacletForTests.parseTerm("p(one, zero)");	
	ImmutableList<RuleSet> listofHeuristic=ImmutableSLList.<RuleSet>nil();
        listofHeuristic=listofHeuristic.prepend(h3);
        PosInOccurrence pos = new PosInOccurrence(new SequentFormula(term_p1),
                PosInTerm.getTopLevel(), true);
  	assertTrue("Noninteractive antecrule is not in list, but none of its"+
		   "heuristics is active.",
		   isRuleIn(variante_one.getAntecedentTaclet(pos,
			    new IHTacletFilter (true, listofHeuristic),
   			    null),ruleRewriteNonH1H2)); 

 	assertTrue("Noninteractive antecrule is in list, but one of its "+
		   "heuristics is active.",
		   !isRuleIn(variante_one.getAntecedentTaclet(pos,
		             new IHTacletFilter (true, listofHeuristic.prepend(h1)),
			     null),ruleRewriteNonH1H2));  

  	assertTrue("Noninteractive nofindrule is not in list, but none of its "+
		   "heuristics is active.",
		   isRuleIn(variante_one.getNoFindTaclet(new IHTacletFilter (true, ImmutableSLList.<RuleSet>nil()),
   			    null),ruleNoFindNonH1H2H3));  

 	assertTrue("Noninteractive nofindrule is in list, but one of its "+
		   "heuristics is active.",
		   !isRuleIn(variante_one.getNoFindTaclet(new IHTacletFilter (true, listofHeuristic), null),ruleNoFindNonH1H2H3));
	
    }


    public void testShownIfHeuristicFits() {
        Services services = new Services(AbstractProfile.getDefaultProfile());
        ImmutableList<RuleSet> listofHeuristic=ImmutableSLList.<RuleSet>nil();
	listofHeuristic=listofHeuristic.prepend(h3).prepend(h2);

	Term term_p1 = TacletForTests.parseTerm("p(one, zero)");	

        SequentFormula cfma = new SequentFormula(term_p1);
        
        PosInOccurrence posSucc  = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), false);
        
  	assertTrue("ruleSucc has no heuristics, but is"+
		   " not in succ list.",
		   isRuleIn(variante_one.getSuccedentTaclet(posSucc,
		            new IHTacletFilter (true, listofHeuristic),
		            services), ruleSucc)); 
        
  	assertTrue("ruleSucc has no heuristics, but is"+
		   " in rewrite list.",
		   !isRuleIn(variante_one.getRewriteTaclet(posSucc, new IHTacletFilter (true, listofHeuristic),
		             services),ruleSucc)); 


  	assertTrue("ruleSucc has no heuristics, but is"+
		   " in heuristic succ list.",
		   !isRuleIn(variante_one.getSuccedentTaclet(posSucc,
		             new IHTacletFilter (false, listofHeuristic),
		             services),ruleSucc)); 

  	assertTrue("ruleSucc has no heuristics, but is"+
		   " in heuristic of nofind list.",
		   !isRuleIn(variante_one.getNoFindTaclet(new IHTacletFilter (false,
   			     listofHeuristic), services),ruleSucc));
    }

    public void testNoMatchingFindRule() {
        Services services = new Services(AbstractProfile.getDefaultProfile());
        ImmutableList<RuleSet> listofHeuristic=ImmutableSLList.<RuleSet>nil();

	Term term_p2 = TacletForTests.parseTerm("\\forall nat z; p(z, one)").sub(0);
	
        PosInOccurrence posAntec = new PosInOccurrence(new SequentFormula(term_p2),
                PosInTerm.getTopLevel(), true);
        PosInOccurrence posSucc = new PosInOccurrence(new SequentFormula(term_p2),
                PosInTerm.getTopLevel(), true);

        
 	assertTrue("rule matched, but no match possible",
		   !isRuleIn(variante_one.getAntecedentTaclet(posAntec,
		                                              new IHTacletFilter (true, listofHeuristic),
		                                              services), 
			     ruleRewriteNonH1H2));
 

	listofHeuristic=listofHeuristic.prepend(h3).prepend(h2).prepend(h1);

 	assertTrue("ruleSucc matched but matching not possible",
		   !isRuleIn(variante_one.getSuccedentTaclet(posSucc,
		             new IHTacletFilter (true, listofHeuristic),
			     services),ruleSucc));		
    }

    public void testMatchConflictOccurs() {
        Services services = new Services(AbstractProfile.getDefaultProfile());
        TacletIndex ruleIdx=new TacletIndex();
	ruleIdx.add(ruleRewriteNonH1H2);
	ruleIdx.add(ruleNoFindNonH1H2H3);
	ruleIdx.add(ruleAntecH1);
	ruleIdx.add(ruleSucc);
	ruleIdx.add(ruleMisMatch);

	Term term_p4 = TacletForTests.parseTerm("p(zero, one)");

	ImmutableList<RuleSet> listofHeuristic=ImmutableSLList.<RuleSet>nil();
        PosInOccurrence posAntec = new PosInOccurrence(new SequentFormula(term_p4),
                PosInTerm.getTopLevel(), true);
	
 	assertTrue("rule matched, but no match possible",
		   !isRuleIn(ruleIdx.getAntecedentTaclet(posAntec,
		             new IHTacletFilter (true, listofHeuristic),
   			     services),ruleMisMatch));
 
    }

    public void testNotFreeInYConflict() {
	TacletIndex ruleIdx=new TacletIndex();
	ruleIdx.add(notfreeconflict);

	Term term_p5 = TacletForTests.parseTerm("\\forall nat z; p(f(z), z)");
	SequentFormula cfma_p5 = new SequentFormula(term_p5);
	Sequent seq_p5 = Sequent.createAnteSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insertFirst(cfma_p5).semisequent());
	PosInOccurrence pio_p5 = new PosInOccurrence
	    (cfma_p5, PosInTerm.getTopLevel(), true);
        RuleAppIndex appIdx = createGoalFor(seq_p5, ruleIdx);
		  
	assertTrue("No rule should match",
		   !isRuleIn(appIdx.getTacletAppAt
			     (TacletFilter.TRUE, pio_p5,
			     null),
			     notfreeconflict));

	Term term_p6 = TacletForTests.
	    parseTerm("\\forall nat z; p(zero, z)");

	SequentFormula cfma_p6 = new SequentFormula(term_p6);
	Sequent seq_p6 = Sequent.createAnteSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insertFirst(cfma_p6).semisequent());
	PosInOccurrence pio_p6 = new PosInOccurrence
	    (cfma_p6, PosInTerm.getTopLevel(), true);
	appIdx = createGoalFor(seq_p6, ruleIdx);

	assertTrue("One rule should match", isRuleIn
		   (appIdx.
		    getTacletAppAt(TacletFilter.TRUE, pio_p6,
		                   null),
		    notfreeconflict));
	    
    }

    private RuleAppIndex createGoalFor(Sequent seq_p5, TacletIndex ruleIdx) {
        final Node node_p5 =
            new Node (new Proof (new Services(AbstractProfile.getDefaultProfile())), seq_p5);
        final BuiltInRuleAppIndex builtinIdx =
            new BuiltInRuleAppIndex (new BuiltInRuleIndex ());
        final Goal goal_p5 =
            new Goal (node_p5, new RuleAppIndex (ruleIdx, builtinIdx, node_p5.proof().getServices()));
	return goal_p5.ruleAppIndex ();
    }


}