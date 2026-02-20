/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.util.Optional;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

public class TestParser {
    /**
     * Test that {@code KeYParser} correctly translates {@code \include} statements into
     * {@code Includes} instances.
     * <p>
     * Previously, this was broken because the token source name, which is needed for includes
     * specified by a path relative to the KeY file's location, was uninitialized.
     *
     * @throws IOException
     */
    @Test
    public void testRelativeInclude() throws IOException {
        // `include.key` does not actually exist since `RuleSource#initRuleFile`
        // does not care for the moment
        final File include = new File("include.key");
        assumeTrue(include.exists());

        final Includes expected = new Includes();
        expected.put(include.toString(), RuleSourceFactory.initRuleFile(include.toURI().toURL()));
        final String keyFile = "\\include \"" + include.getPath() + "\";";
        KeyAst.File file = ParsingFacade.parseFile(CharStreams.fromString(keyFile));
        Includes actual = file.getIncludes(new File(".").toURI().toURL());

        // `Includes` does not provide an `Object#equals()` redefinition for the
        // moment, at least compare the list of filenames
        assertEquals(actual.getIncludes(), expected.getIncludes());
    }


    @Test
    public void testGenericSort() throws IOException {
        String content = """
                \\sorts { \\generic gen; }\s

                \\rules { SomeRule { \\find(gen::instance(0)) \\replacewith(false) }; }
                \\problem { true }""";

        Services services = TacletForTests.services();
        KeyIO io = new KeyIO(services);
        KeyIO.Loader loader = io.load(content);
        loader.parseFile().loadComplete();
        loader.loadProblem();
    }


    @Test
    public void testIssue1566() throws ProblemLoaderException {
        var file = HelperClassForTests.TESTCASE_DIRECTORY.resolve("issues/1566/a.key");
        KeYEnvironment.load(file);
    }

    @Test()
    public void testIssue39() {
        assertThrows(ProblemLoaderException.class, () -> {
            var file = HelperClassForTests.TESTCASE_DIRECTORY.resolve("issues/39/A.java");
            KeYEnvironment.load(file, null, null, null);
        });

    }

    // Handled by javac, javaparser does no type checking
    @Disabled
    @Test
    void testConstantEvaluationError() throws MalformedURLException {
        var file =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("parserErrorTest/AssignToArray.java");
        var problemLoaderException = assertThrows(ProblemLoaderException.class, () -> {
            KeYEnvironment.load(file, null, null, null);
        });
        var error = (HasLocation) problemLoaderException.getCause();
        var location = error.getLocation();
        assertEquals(4, location.getPosition().line());
        assertEquals(9, location.getPosition().column());
        assertEquals(Optional.of(file.toUri()), location.getFileURI());
    }
}
