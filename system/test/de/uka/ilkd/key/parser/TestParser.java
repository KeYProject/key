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

package de.uka.ilkd.key.parser;

import java.io.File;
import java.io.IOException;

import junit.framework.Assert;
import junit.framework.TestCase;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import org.antlr.runtime.RecognitionException;

public class TestParser extends TestCase {
    /**
     * Test that {@code KeYParser} correctly translates {@code \include}
     * statements into {@code Includes} instances.
     * 
     * Previously, this was broken because the token source name, which is
     * needed for includes specified by a path relative to the KeY file's
     * location, was uninitialized.
     * 
     * @throws org.antlr.runtime.RecognitionException
     * @throws IOException
     */
    public void testRelativeInclude() throws RecognitionException, IOException {
	// `include.key` does not actually exist since `RuleSource#initRuleFile`
	// does not care for the moment
	final File include = new File("include.key");
	final Includes expected = new Includes();
	expected.put(include.toString(),
		RuleSourceFactory.initRuleFile(include.toURL()));

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