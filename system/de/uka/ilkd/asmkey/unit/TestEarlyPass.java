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

import java.io.IOException;

import de.uka.ilkd.asmkey.parser.ast.AstMultiPassDeclaration;
import de.uka.ilkd.asmkey.parser.ast.AstSinglePassDeclaration;
import de.uka.ilkd.asmkey.parser.ast.AstUnitDeclarations;
import de.uka.ilkd.asmkey.parser.env.DeclarationEnvironment;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParser;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.parser.ParserException;


/**
 * the first pass of the tree parsing collects
 * the symbols into the environment namespaces.
 * the goal of the test is to check these symbols are
 * properly loaded. This is done by queriing the different
 * namespaces, in relative and absolute naming.
 *
 * We load the units as for the unit manager. put stop at
 * the first pass.
 */
public class TestEarlyPass extends AbstractTestUnit {

    private Unit unit;

    protected DeclarationParserFactory factory() {
	return new 
	    DeclarationParserFactory() {
		public DeclarationParser getParser(DeclarationEnvironment env) {
		    return new DeclarationParser(env) {
			    
			    public void parse(AstUnitDeclarations decls) throws ParserException {
				AstSinglePassDeclaration[] early =
				    decls.getEarlySinglePassDeclarations();
				AstMultiPassDeclaration[] multi = 
				    decls.getMultiPassDeclarations();
				for (int i = 0; i < early.length; ++i) {
				    parseSingle(early[i]);
				}
				for (int i = 0; i < multi.length; i++) {
				    parseFirstPass(multi[i]);
				}
			    }
			    
			};
		}
	    };
    }

    protected UnitListener listener() { return new UnitUtil.EmptyUnitListener(); }

    public void testFirstPass() throws UnitException, IOException {
	String[] sorts = getLines("earlyPassSorts");
	String[] schemaVars = getLines("earlyPassVars");
	String[] funcs = getLines("earlyPassFuncs");
	String[] rules = getLines("earlyPassRules");

	managerLoad();

	unit = manager.graph().get(new Name("U1"));
	assertNotNull("The unit U1 should exists.", unit);

	assertExists(sorts, RestrictedSymbol.SORT);
	assertExists(schemaVars, RestrictedSymbol.SCHEMA_VARIABLE);
	assertExists(funcs, RestrictedSymbol.FUNCTION);
	assertExists(rules, RestrictedSymbol.ASMRULE);
    }

    public void assertExists(String[] tests, int kind) throws UnitException {
	for (int i =0; i<tests.length; i++) {
	    assertTrue("The symbol " + tests[i] + " of kind " + 
			  RestrictedSymbol.getStringForType(kind) + " should exist.",
			  unit.containsRestrictedSymbol
			  (new RestrictedSymbol(kind, new Name(tests[i]))));
	}
    }
    
    public String testName() {
	return "TestEarlyPass";
    }

}
