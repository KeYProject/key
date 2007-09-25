// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.key.logic.Name;

/**
 * to test the unit manager
 */
public class TestUnitManager extends AbstractTestUnit {
    
    protected UnitListener listener() throws IOException {
	return TextUnitListener.fileUnitListener
		(new File(keyhome + "/system/unit_manager.log"));
    }

    protected DeclarationParserFactory factory() {
	return DeclarationParserFactory.DEFAULT;
    }
    
    public void lookupTest() throws IOException, UnitException{
	Unit u1 = manager.graph().get(new Name("U1"));

	assertNotNull("The unit U1 should exists.", u1);
	assertNotNull("The constant U1.true should exists.",
		   u1.funcNS().lookup("U1.true"));


	String[] taclets = getLines("testUnitManagerTaclets");
	String[] props = getLines("testUnitManagerProps");
	assertExists(taclets, RestrictedSymbol.TACLET, u1);
	assertExists(props, RestrictedSymbol.PROPOSITION, u1);
	assertTrue("Problem with number of taclets.", 0 != u1.getSetOfTaclet().size());

	manager.getOrderedUnits();
    }

    public void assertExists(String[] tests, int kind, Unit unit) throws UnitException {
	for (int i =0; i<tests.length; i++) {
	    assertNotNull("The symbol " + tests[i] + " of kind " + 
		       RestrictedSymbol.getStringForType(kind) + " should exist.",
		       unit.getNSForType(kind).lookup(new Name(tests[i])));
	}
    }
    

    public void testUnitManager() throws IOException, UnitException {
	managerLoad();
	lookupTest();
    }

    public void tearDown() {
	listener.stopLogging();
    }


    public String testName() {
	return "TestUnitManager";
    }

}
