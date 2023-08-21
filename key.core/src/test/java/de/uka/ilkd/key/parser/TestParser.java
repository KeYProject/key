/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.PosConvertException;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.antlr.v4.runtime.CharStreams;
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
        String content = "\\sorts { \\generic gen; } \n\n"
            + "\\rules { SomeRule { \\find(gen::instance(0)) \\replacewith(false) }; }\n"
            + "\\problem { true }";

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

    @Test()
    public void testIssue39() {
        assertThrows(ProblemLoaderException.class, () -> {
            File file = new File(HelperClassForTests.TESTCASE_DIRECTORY, "issues/39/A.java");
            KeYEnvironment<DefaultUserInterfaceControl> env =
                KeYEnvironment.load(file, null, null, null);
        });

    }

    @Test
    void testConstantEvaluationError() throws MalformedURLException {
        var file =
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "parserErrorTest/AssignToArray.java");
        var problemLoaderException = assertThrows(ProblemLoaderException.class, () -> {
            KeYEnvironment<DefaultUserInterfaceControl> env =
                KeYEnvironment.load(file, null, null, null);
        });
        var error = (PosConvertException) problemLoaderException.getCause();
        assertEquals(4, error.getPosition().line());
        assertEquals(9, error.getPosition().column());
        assertEquals(file.toURI(), error.getLocation().getFileURI().orElseThrow());

    }
}
