// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import junit.framework.TestCase;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletForTests;


/** 
 * class tests the creation of proof obligations of taclets
 */
public class TestProofObligationCreation extends TestCase {

    public TestProofObligationCreation(String name) {
	super(name);
    }

    public void setUp() {
	TacletForTests.setStandardFile(TacletForTests.testRules);
	TacletForTests.parse();
    }

    // Currently only the creation of proof obligations is performed,
    // the result is not checked
    public void testCreation () {
	createPO ( "testPO0", 1 );
	createPO ( "testPO1", 1 );
	createPO ( "testPO2", 2 );
	createPO ( "testPO3", 2 );
	createPO ( "testPO4", 1 );
	createPO ( "testPO5", 9 );
    }

    private void createPO ( String p_tacletName,
                            int    p_expectedNumberOfPOParts ) {
	TacletForTests.getJavaInfo().readJavaBlock("{}");
	NoPosTacletApp app = TacletForTests.getRules().lookup ( p_tacletName );
	POBuilder pob = new POBuilder ( app, TacletForTests.services () );
	pob.build ();
	
	assertTrue ( "Expected the proof obligation to consist of " +
	             p_expectedNumberOfPOParts + ", but got " +
	             pob.getNumberOfPOParts() + " parts.",
	             p_expectedNumberOfPOParts == pob.getNumberOfPOParts() );
    }

}
