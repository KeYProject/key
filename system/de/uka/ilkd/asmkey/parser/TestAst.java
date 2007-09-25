// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.parser;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;

import junit.framework.Assert;
import de.uka.ilkd.asmkey.parser.ast.*;
import de.uka.ilkd.asmkey.util.TestUtil;
import de.uka.ilkd.key.parser.ParserException;

public class TestAst extends TestUtil {

    public static final AstFactory af = new AstFactoryImpl();

    /** as the identifiers are a complex token, we test them
     * thoroughly.
     */
    public void testIdent() throws IOException {
	assertIdentifiers("testIdents");
    }

    /** 
     * We test bigidents
     */
    public void testBigIdent() throws IOException {
	assertIdentifiers("testBigIdents");
    }
    
    /**
     * We test stepident
     */
    public void testStepIdent() throws IOException {
	assertIdentifiers("testStepIdents");
    }

    /**
     * We test strings that do not form idents.
     */
    public void testNoIdents() throws IOException{
	String[] test_strings = getLines("testNoIdents");
	
	StringParsitorFactory[] factories = new StringParsitorFactory[] {
	    new IdentParsitorFactory(),
	    new BigIdentParsitorFactory(),
	    new StepIdentParsitorFactory(),
	};

	for(int i = 0; i<test_strings.length; i++) {
	    for (int j=0; j<factories.length; j++) {
		parseStringAndFail(factories[j].createStringParsitor(test_strings[i]));
	    }
	}
    }

    /**
     * We test terms
     */
    public void testTerms() throws IOException {
	assertParseFile("testTerms");
	assertNoParseFile("testNoTerms");
    }

    /**
     * We test sorts declarations
     */
    public void testSortDecls() throws IOException {
	assertParseFile("testSortDecls");
	assertNoParseFile("testSortNoDecls");
    }

    /** 
     * We test schema variables declarations
     */
    public void testSchemaDecls() throws IOException {
	assertParseFile("testSchemaDecls");
	assertNoParseFile("testSchemaNoDecls");
    }

    /**
     * We test predicate declarations
     */
    public void testPredicateDecls() throws IOException {
	 assertParseFile("testPredicateDecls");
    }
    
    /**
     * We test function declarations
     */
    public void testFunctionDecls() throws IOException {
	assertParseFile("testFunctionDecls");
	assertNoParseFile("testFunctionNoDecls");
    }

    /**
     * We test units, imports and declarations from a file. U1.
     */
    public void testAst() throws java.io.FileNotFoundException {
	try {
	    File file = new File(keyhome + "/system/resources-asmkey/tests/units/U1.unit");
	    AstUnit u1 = AstParser.parseUnit(file);
	} catch (ParserException e) {
	    Assert.fail(e.getMessage() + " ---- " + e.getLocation());
	}
    }


    /* --- private methods --- */

    private void fail(ParserException e) {
	Assert.fail(e.getMessage() + " ---- " + e.getLocation());
    }

    private Object parseStringOrFail(StringParsitor p) {
	try {
	    return p.parse();
	} catch (ParserException e) {
	    fail(e);
	    return null;
	}
    }

    private void parseStringAndFail(StringParsitor p) {
	try {
	    p.parse();
	    Assert.fail("The string " + p.getString() + " should fail in the " +
			p + " .");
	} catch (ParserException e) {
	    Assert.assertTrue(true);
	}
    }

    private void assertIdentifiers(String name) throws IOException {
	String[] symbols = getLines(name);
	StringParsitorFactory factory = getParsitorFactory(symbols[0]);
	for (int i = 1; i<symbols.length; i++) {
	    Identifier id = (Identifier) parseStringOrFail(factory.createStringParsitor(symbols[i]));
	    Assert.assertEquals("TestAst:should be equal:" + id + ";" + symbols[i],
				id.getText(), symbols[i]);
	}
    }

    private void assertParseFile(String name) throws IOException {
	String[] decls = getLines(name);
	StringParsitorFactory factory = getParsitorFactory(decls[0]);
	for (int i=1; i<decls.length; i++) {
	    parseStringOrFail(factory.createStringParsitor(decls[i]));
	}
    }

    private void assertNoParseFile(String name) throws IOException {
	String[] no_decls = getLines(name);
	StringParsitorFactory factory = getParsitorFactory(no_decls[0]);
	for(int i=1; i<no_decls.length; i++) {
	    parseStringAndFail(factory.createStringParsitor(no_decls[i]));
	}
    }

    private StringParsitorFactory getParsitorFactory(String in) throws IOException {
	String line = in.trim();
	Class factory;
	if (line != null) {
	    if(line.equals("IdentParsitorFactory")) {
		return new IdentParsitorFactory();
	    } else if (line.equals("BigIdentParsitorFactory")) {
		return new BigIdentParsitorFactory();
	    } else if (line.equals("StepIdentParsitorFactory")) {
		return new StepIdentParsitorFactory();
	    } else if (line.equals("TermParsitorFactory")) {
		return new StringParsitorFactory() {
			public StringParsitor createStringParsitor(String s) {
			    return new StringParsitor(s) {
				    public Object internParse()
					throws antlr.TokenStreamException,
					       antlr.RecognitionException
				    {
					return parser.top_term();
				    }
				    
				    public String toString() {
					return "TermParsitor";
				    }
				};
			}
		    };
	    } else if(line.equals("SortDeclarationParsitorFactory")) {
		return new StringParsitorFactory() {
			public StringParsitor createStringParsitor(String s) {
			    return new StringParsitor(s) {
				    public Object internParse()
					throws antlr.TokenStreamException,
					       antlr.RecognitionException
				    {
					return parser.top_sortDeclaration();
				    }
				    
				    public String toString() {
					return "SortDeclarationParsitor";
				    }
				};
			}
		    };
	    } else if (line.equals("SchemaDeclarationParsitorFactory")) {
		return new SchemaDeclarationParsitorFactory();
	    } else if (line.equals("PredicateDeclarationParsitorFactory")) {
		return new PredicateDeclarationParsitorFactory();
	    } else if (line.equals("FunctionDeclarationParsitorFactory")) {
		return new StringParsitorFactory() {
			public StringParsitor createStringParsitor(String s) {
			    return new StringParsitor(s) {
				    public Object internParse()
					throws antlr.TokenStreamException,
					       antlr.RecognitionException
				    {
					return parser.top_functionDeclaration();
				    }
				    
				    public String toString() {
					return "FunctionDeclarationParsitor";
				    }
				};
			}
		    };
	    }
	    
	    else {
		Assert.fail("The StringParsitorFactory " + line.trim() + " does not exist.");
	    }  
	}
	Assert.fail("The test file was empty");
	return null;
    }
}




abstract class StringParsitor extends AbstractAstParsitor {

    private String string;

    public StringParsitor(String s) {
	super(new StringReader(s), TestAst.af);
	this.string = s;
    }
    
    public String getString() {
	return string;
    }

} 

abstract class StringParsitorFactory {

    abstract public StringParsitor createStringParsitor(String s);

}

class IdentParsitorFactory extends StringParsitorFactory {
    
    public StringParsitor createStringParsitor(String s) {
	return new StringParsitor(s) {
		protected Object internParse()
		    throws antlr.TokenStreamException, antlr.RecognitionException
		{
		    return parser.top_ident();
		}
		
		public String toString() {
		    return "IdentParsito";
		}
	    };
    }

}

class BigIdentParsitorFactory extends StringParsitorFactory {
    
    public StringParsitor createStringParsitor(String s) {
	return new StringParsitor(s) {
		protected Object internParse()
		    throws antlr.TokenStreamException, antlr.RecognitionException
		{
		    return parser.top_bigident();
		}

		public String toString() {
		    return "BigIdentParsitor";
		}
	    };
    }
}

class StepIdentParsitorFactory extends StringParsitorFactory {
    
    public StringParsitor createStringParsitor(String s) {
	return new StringParsitor(s) {
		protected Object internParse()
		    throws antlr.TokenStreamException, antlr.RecognitionException
		{
		    return parser.top_stepident();
		}

		public String toString() {
		    return "StepIdentParsitor";
		}
	    };
    }
}

class SchemaDeclarationParsitorFactory extends StringParsitorFactory {
    public StringParsitor createStringParsitor(String s) {
	return new StringParsitor(s) {
		public Object internParse() 
		    throws antlr.TokenStreamException, antlr.RecognitionException 
		{
		    return parser.top_schemaDeclaration();
		}
		
		public String toString() {
		    return "SchemaDeclarationParsitor";
		}
	    };
    }
}

class PredicateDeclarationParsitorFactory extends StringParsitorFactory {
    public StringParsitor createStringParsitor(String s) {
	return new StringParsitor(s) {
		public Object internParse()
		    throws antlr.TokenStreamException, antlr.RecognitionException
		{
		    return parser.top_predicateDeclaration();
		}

		public String toString() {
		    return "PredicateDeclarationParsitor";
		}
	    };
    }
}
