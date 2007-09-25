// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit.base;

import junit.framework.TestCase;
import de.uka.ilkd.asmkey.parser.ast.AstFactory;
import de.uka.ilkd.asmkey.parser.ast.AstFactoryImpl;
import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.parser.ast.Identifier;
import de.uka.ilkd.asmkey.unit.UnitException;

public class TestBase extends TestCase {

    public void testBase() throws UnitException {
	AstFactory factory = new AstFactoryImpl();
	AstUnit test = factory.createAstUnit(null, new Identifier(null, "Int"), null, null, null);
	Int.initialize(test);
	assertTrue("static methods are not overloaded....", Int.hasBeenInitialized());
    }

}
