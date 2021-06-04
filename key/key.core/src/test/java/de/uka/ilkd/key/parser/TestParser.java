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

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.antlr.runtime.RecognitionException;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

public class TestParser {
    /**
     * Test that {@code KeYParser} correctly translates {@code \include}
     * statements into {@code Includes} instances.
     * <p>
     * Previously, this was broken because the token source name, which is
     * needed for includes specified by a path relative to the KeY file's
     * location, was uninitialized.
     *
     * @throws org.antlr.runtime.RecognitionException
     * @throws IOException
     */
    @Test
    public void testRelativeInclude() throws RecognitionException, IOException {
        // `include.key` does not actually exist since `RuleSource#initRuleFile`
        // does not care for the moment
        final File include = new File("include.key");
        Assume.assumeTrue(include.exists());

        final Includes expected = new Includes();
        expected.put(include.toString(),
                RuleSourceFactory.initRuleFile(include.toURI().toURL()));
        final String keyFile = "\\include \"" + include.getPath() + "\";";
        KeyAst.File file = ParsingFacade.parseFile(CharStreams.fromString(keyFile));
        Includes actual = file.getIncludes(new File(".").toURI().toURL());

        // `Includes` does not provide an `Object#equals()` redefinition for the
        // moment, at least compare the list of filenames
        Assert.assertEquals(actual.getIncludes(), expected.getIncludes());
    }


    @Test
    public void testGenericSort() throws RecognitionException, IOException {
        String content = "\\sorts { \\generic gen; } \n\n" +
                "\\rules { SomeRule { \\find(gen::instance(0)) \\replacewith(false) }; }\n" +
                "\\problem { true }";

        Services services = TacletForTests.services();
        KeyIO io = new KeyIO(services);
        KeyIO.Loader loader = io.load(content);
        loader.parseFile().loadComplete();
        loader.loadProblem();
    }


    @Test
    public void testIssue1566() throws ProblemLoaderException {
        File file = new File(HelperClassForTests.TESTCASE_DIRECTORY, "issues/1566/a.key");
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file);
    }
}