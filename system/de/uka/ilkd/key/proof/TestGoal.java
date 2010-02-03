// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.rule.TacletForTests;

/** class tests the goal, especially the split and set back mechanism.
*/


public class TestGoal extends TestCase {

    Proof proof;

    public TestGoal(String name) {
	super(name);
    }

    public void setUp() {
	TacletForTests.parse();
	proof = new Proof(new Services());

    }
    
    public void tearDown() {
        proof = null;
    }


    public void testSetBack0() {
	Sequent seq=Sequent.createSuccSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0,new ConstrainedFormula
		(TacletForTests.parseTerm("A"))).semisequent());
	Goal g=new Goal(new Node(proof, seq), 
			new RuleAppIndex(new TacletAppIndex(new TacletIndex()),
					 new BuiltInRuleAppIndex(new BuiltInRuleIndex())));
	ListOfGoal lg=g.split(3);
	lg.head().addNoPosTacletApp(TacletForTests.getRules().lookup("imp_right"));
	lg.tail().head()
	    .addNoPosTacletApp(TacletForTests.getRules().lookup("imp_left"));
	lg.tail().tail().head()
	    .addNoPosTacletApp(TacletForTests.getRules().lookup("or_right"));
	//just check if the test is trivially correct because of rules not found
	assertNotNull(lg.head().indexOfTaclets().lookup("imp_right"));
	ListOfGoal lg0=lg.head().split(3);
	ListOfGoal lg00=lg0.tail().head().split(8);
	ListOfGoal lg1=lg.tail().tail().head().split(2);
	ListOfGoal res=lg.tail().head().setBack(lg1.append(lg00)
						.append(lg0.head())
					.append(lg0.tail().tail().head())
						.append(lg.tail().head()));
	assertTrue(res.size()==1);
	assertNull("Taclet Index of set back goal contains rule \"imp-right\" that were not "
		   +"there before",
		   res.head().indexOfTaclets().lookup("imp_right"));
	assertNull("Taclet Index of set back goal contains rule \"or-right\"that were not "
		   +"there before",
		   res.head().indexOfTaclets().lookup("or_right"));
	assertNull("Taclet Index of set back goal contains rule \"imp-left\" that were not "
		   +"there before", 
		   res.head().indexOfTaclets().lookup("imp_left"));

	       
    }   


    public void invalidtestSetBack1() {
	Sequent seq=Sequent.createSuccSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert(0,new ConstrainedFormula
		(TacletForTests.parseTerm("A"))).semisequent());
	Goal g=new Goal(new Node(proof, seq), 
			new RuleAppIndex(new TacletAppIndex(new TacletIndex()),
					 new BuiltInRuleAppIndex
					 (new BuiltInRuleIndex())));
	ListOfGoal lg=g.split(3);
	lg.head().addNoPosTacletApp(TacletForTests.getRules().lookup("imp_right"));
	lg.tail().head()
	    .addNoPosTacletApp(TacletForTests.getRules().lookup("imp_left"));
	lg.tail().tail().head()
	    .addNoPosTacletApp(TacletForTests.getRules().lookup("or_right"));
	//just check if the test is trivially correct because of rules not found
	assertNotNull(lg.head().indexOfTaclets().lookup("imp_right"));

	ListOfGoal lg0=lg.head().split(4);
	lg0.head().addNoPosTacletApp(TacletForTests.getRules().lookup("or_left"));
	lg0.tail().head().addNoPosTacletApp(TacletForTests.getRules()
					  .lookup("or_left"));
	ListOfGoal lg1=lg.tail().tail().head().split(2);
	ListOfGoal res=lg0.tail().head().setBack(lg1.append(lg0)
						.append(lg.tail().head()));
	assertTrue(res.size()==4);

	assertTrue(res.contains(lg1.head()));
	assertNotNull(lg1.head().indexOfTaclets().lookup("or_right"));
	//	assertTrue(lg1.head().indexOfTaclets().lookup("or_left")==null);
	res=res.removeAll(lg1.head());

	assertTrue(res.contains(lg1.tail().head()));
	assertNotNull(lg1.tail().head().indexOfTaclets().lookup("or_right"));
	//	assertTrue(lg1.tail().head().indexOfTaclets().lookup("or_left")==null);
	res=res.removeAll(lg1.tail().head());	
	if (res.head().indexOfTaclets().lookup("imp_right")!=null) {
	    assertNotNull (res.tail().head().indexOfTaclets().lookup("imp_left"));
	} else {
	    assertNotNull (res.head().indexOfTaclets().lookup("imp_left"));
	    assertNotNull (res.tail().head().indexOfTaclets().lookup("imp_right"));
	}
	assertNull(res.head().indexOfTaclets().lookup("or_left"));
	assertNull(res.tail().head().indexOfTaclets().lookup("or_left"));
	
    }   

 
}


