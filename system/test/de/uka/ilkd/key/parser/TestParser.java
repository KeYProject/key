package de.uka.ilkd.key.parser;

import java.io.File;
import java.io.IOException;

import junit.framework.Assert;
import junit.framework.TestCase;
import antlr.ANTLRException;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.io.RuleSource;

public class TestParser extends TestCase {
    /**
     * Test that {@code KeYParser} correctly translates {@code \include}
     * statements into {@code Includes} instances.
     * 
     * Previously, this was broken because the token source name, which is
     * needed for includes specified by a path relative to the KeY file's
     * location, was uninitialized.
     * 
     * @throws ANTLRException
     * @throws IOException
     */
    public void testRelativeInclude() throws ANTLRException, IOException {
	// `include.key` does not actually exist since `RuleSource#initRuleFile`
	// does not care for the moment
	final File include = new File("include.key");
	final Includes expected = new Includes();
	expected.put(include.toString(),
		RuleSource.initRuleFile(include.toURL()));

	final String keyFile = "\\include \"" + include.getPath() + "\";";
	final KeYLexerF lexer = new KeYLexerF(keyFile,
		"No file. Test case TestParser#testRelativeInclude()", null);
	final KeYParserF parser = new KeYParserF(ParserMode.DECLARATION, lexer);
	parser.parseIncludes();

	// `Includes` does not provide an `Object#equals()` redefinition for the
	// moment, at least compare the list of filenames
	final Includes actual = parser.getIncludes();
	Assert.assertEquals(actual.getIncludes(), expected.getIncludes());
    }
}