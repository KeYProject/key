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

import de.uka.ilkd.asmkey.logic.DerivedFunction;
import de.uka.ilkd.asmkey.logic.NonRigidDerivedFunction;
import de.uka.ilkd.asmkey.logic.ParsingDerivedFunction;
import de.uka.ilkd.asmkey.logic.RigidDerivedFunction;
import de.uka.ilkd.asmkey.parser.ast.AstMultiPassDeclaration;
import de.uka.ilkd.asmkey.parser.ast.AstSinglePassDeclaration;
import de.uka.ilkd.asmkey.parser.ast.AstUnitDeclarations;
import de.uka.ilkd.asmkey.parser.env.DeclarationEnvironment;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParser;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.asmkey.parser.tree.DerivedFunctionParser;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigid;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.parser.ParserException;

/** to test final pass for multiple pass
 * symbols; just after the replacement
 * @see DerivedFunctionParser
 * @see DeclarationParser
 * @see DeclarationParserFactory
 */ 
public class TestFinalPass extends AbstractTestUnit {
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
				AstSinglePassDeclaration[] late = 
				    decls.getLateSinglePassDeclarations();
				for (int i = 0; i < early.length; ++i) {
				    parseSingle(early[i]);
				}
				for (int i = 0; i < multi.length; i++) {
				    parseFirstPass(multi[i]);
				}
				for (int i = 0; i < multi.length; i++) {
				    parseSecondPass(multi[i]);
				}
				DerivedFunctionParser parser = 
				    new DerivedFunctionParser(this.env, this.deriveds);
				parser.doAnalysis(); 
				parser.replaceSymbols();
			    }
			};
		}
	    };
    }

    protected UnitListener listener() { return new UnitUtil.EmptyUnitListener(); }

    public void testFinalPass() throws UnitException, IOException {
	String[] rec = getLines("secondPassFuncsRec");
	String[] rigid = getLines("secondPassFuncsRigid");

	managerLoad();

	final Unit u1 = manager.graph().get(new Name("U1"));

	assertBoolean(rec, new Tester() {
		public Unit unit() { return u1; }
		public String message(){
		    return "The recursive information has been wrongly computed for the function ";
		}
		public boolean test(DerivedFunction f) {
		    return f.isRecursive();
		}
	    });
	assertBoolean(rigid, new Tester() {
		public Unit unit() { return u1; }
		public String message() {
		    return "The rigid information has been wrongly computed for the function ";
		}
		public boolean test(DerivedFunction f) {
		    return !(f instanceof NonRigid);
		}
	    });
	assertNoParsingDerivedFunctions(u1);
    }

    private void assertBoolean(String[] line, Tester t) {
	String[] test;
	DerivedFunction f;
	for(int i = 0; i<line.length; i++) {
	    test = line[i].split(" ");
	    f = (DerivedFunction) t.unit().funcNS().lookup(test[0]);
	    assertEquals(t.message() + test[0] + ": ",
			 Boolean.valueOf(test[1]).booleanValue(),
			 t.test(f));
	}
    }

    private void assertNoParsingDerivedFunctions(Unit u) {
	IteratorOfNamed it = u.funcNS().elements().iterator();
	Named element;
	DerivedFunction func;
	while (it.hasNext()) {
	    element = it.next();
	    if (element instanceof NonRigidDerivedFunction || 
		element instanceof RigidDerivedFunction) {
		func = (DerivedFunction) element;
		assertBody(func.body(), func.name());
	    } else if (element instanceof ParsingDerivedFunction) {
		fail("Found an operator still being a ParsingDerivedFunction, op=" + element.name());
	    } else {
		assertTrue(true);
	    }
	}
    }

    private void assertBody(Term term, Name func) {
	Operator op = term.op();
	if (op instanceof ParsingDerivedFunction) {
	    fail("Found an ParsingDerivedFunction in the term of DerivedFunction " + func);
	}
	for(int i=0; i<term.arity(); i++) {
	    assertBody(term.sub(i), func);
	}
    }

    public String testName() {
	return "TestFinalPass";
    }

}
