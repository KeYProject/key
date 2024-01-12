/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser.messages;

import java.io.File;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.ExceptionTools;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.provider.Arguments;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Parameterized JUnit test suite intended for ensuring a certain quality for parser messages. Every
 * test case consists of an erroneous JML file that will be opened by JML parser during a test run.
 * The parser will throw an exception whose contents will be verified.
 * <p>
 * For further documentation, see: key/doc/README.parserMessageTest
 *
 * @author Kai Wallisch
 */
@Disabled("See issue #1500")
public class ParserMessageTest {
    private static final String DOC_FILE = "key/doc/README.parserMessageTest";

    private final List<String> lines;
    private final ProblemLoaderException exception;
    private final Location location;
    private File javaFile;

    /**
     * Method for creating parameters for a parameterized test run. Returned collection is a set of
     * constructor parameters.
     */
    public static Collection<Arguments> data() {
        File testDataDir = new File(HelperClassForTests.TESTCASE_DIRECTORY, "parserMessageTest");
        var data = new LinkedList<Arguments>();
        final var files = testDataDir.listFiles();
        Assertions.assertNotNull(files);
        for (File file : files) {
            if (file.isDirectory()) {
                if (!new File(file, "IGNORE").exists()) {
                    data.add(Arguments.of(file));
                }
            }
        }
        return data;
    }

    public ParserMessageTest(File sourceDir) throws Exception {
        // retrieve the Java file contained in the given source directory:
        for (File file : sourceDir.listFiles()) {
            if (file.getName().endsWith(".java")) {
                assertNull(javaFile, "Found multiple Java files in directory " + sourceDir
                    + "\nCannot unambiguously determine Java source file.");
                javaFile = file;
            }
        }
        assertNotEquals(null, javaFile, "No Java file found in directory " + sourceDir);

        /*
         * Retrieve information about expected parser message from given Java source file.
         */
        lines = Files.readAllLines(javaFile.toPath(), Charset.defaultCharset());
        assertTrue(lines.size() >= 3,
            "Number of lines in file " + javaFile
                + " is less than required minimal number of lines."
                + "\nFirst three lines of tested Java source file must contain "
                + "information about expected parser message. " + "See file " + DOC_FILE
                + " for more information.");

        try {
            KeYEnvironment.load(javaFile);
            fail("Parsing unexpectedly did not throw a " + "ProblemLoaderException for file "
                + javaFile);
            throw new Error(); // to make the rest of the method unreachable
        } catch (ProblemLoaderException e) {
            exception = e;
        }

        location = ExceptionTools.getLocation(exception).orElse(null);

        assertNotNull(location, "Cannot recover error location from Exception: " + exception);

        assertNotNull(location.getFileURI().orElse(null),
            "Couldn't recreate file URL from received exception.");

        assertEquals(javaFile.getAbsoluteFile(), Paths.get(location.getFileURI().get()),
            "Filename retrieved from parser message "
                + "doesn't match filename of originally parsed file.");
    }

    @Test
    public void verifyMessage() {
        String firstLine = lines.get(0);
        assertTrue(firstLine.startsWith("//MSG "),
            "First line of file " + javaFile + " must start with \"//MSG *regexp*\", "
                + "to specify a regular expression for the " + "expected parser message.");
        String parserMessageRegExp = firstLine.substring(6);

        assertTrue(exception.getMessage().matches(parserMessageRegExp),
            "Message of ProblemLoaderException doesn't match regular expression, "
                + "that was specified in file " + javaFile + "\nRequested regular expression: "
                + parserMessageRegExp + "\nRetrieved exception message: " + exception.getMessage());
    }

    @Test
    public void verifyLineNumber() {
        String secondLine = lines.get(1);
        assertTrue(secondLine.startsWith("//LINE "),
            "Second line of file " + javaFile + " must start with \"//LINE *number*\", "
                + "to specify the line number in which a parser error is " + "expected to occur.");
        int expectedLineNumber = Integer.parseInt(secondLine.substring(7));

        assertEquals(expectedLineNumber, location.getPosition().line(),
            "Line number " + location.getPosition().line() + " of retrieved parser message "
                + "doesn't match expected line number " + expectedLineNumber + ".");
    }

    @Test
    public void verifyColumnNumber() {
        String thirdLine = lines.get(2);
        assertTrue(thirdLine.startsWith("//COL "),
            "Third line of file " + javaFile + " must start with \"//COL *number*\", "
                + "to specify the column number in which a parser error is "
                + "expected to occur.");
        int expectedColumnNumber = Integer.parseInt(thirdLine.substring(6));

        assertEquals(expectedColumnNumber, location.getPosition().column(),
            "Column number of retrieved parser message " + "doesn't match expected column number.");
    }

}
