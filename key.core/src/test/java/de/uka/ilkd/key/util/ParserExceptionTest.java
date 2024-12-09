/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Properties;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.provider.Arguments;
import org.opentest4j.AssertionFailedError;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This test case is used to ensure that parser errors are reported with a
 * reasonable error message and the right position pointing into the file.
 * <p>
 * This framework class is versatile and can be used for different parsers,
 * in particular the JML and the JavaDL parsers will be targeted.
 * </p>
 * To add a test case, locate the "exceptional" directory in the resources
 * (below the directory for the package of the refining class) and add single
 * test files (file extension depending on the implementation as returned by
 * ...) that contains an error that should be presented to the user (like
 * syntax errors, unresolved names, ...)
 * <p>
 * See README.md in said directories for information on the meta-data inside
 * the files.
 *
 * @author Mattias Ulbrich
 */
public abstract class ParserExceptionTest {

    /*
     * There are rest cases which are known to be broken.
     * In order to remain productive, these known broken instances
     * are usually deactivated.
     *
     * This can be changed to reactivate the broken test cases
     * (to go bughunting).
     */
    private static final boolean IGNORE_BROKEN = true;

    /**
     * The keys supported in the headers of the files
     */
    private static final Set<String> SUPPORTED_KEYS =
        Set.of("noException", "exceptionClass", "msgContains",
            "msgMatches", "msgIs", "position", "ignore", "broken", "verbose");

    private static final Logger LOGGER = LoggerFactory.getLogger(ParserExceptionTest.class);

    private final static Pattern PROP_LINE =
        Pattern.compile("//\\s*(\\p{Alnum}+)\\s*[:=]\\s*(.*?)\\s*");

    protected static Stream<Arguments> getFiles(String fixedFile, URL fileURL, String extension)
            throws URISyntaxException, IOException {
        assert fileURL != null : "Directory 'exceptional' not found";
        assert fileURL.getProtocol().equals("file") : "Test resources must be in file system";
        Path dir = Paths.get(fileURL.toURI());
        if (fixedFile != null) {
            List<Arguments> list = List.of(Arguments.of(dir.resolve(fixedFile), fixedFile));
            return list.stream();
        }
        return Files.walk(dir).filter(it -> it.getFileName().toString().endsWith(extension))
                .map(it -> Arguments.of(it, it.getFileName()));
    }

    protected abstract void tryLoadFile(Path file) throws Exception;

    // This method does not depend on anything can also be called from other test cases.
    public void parseAndInterpret(Path file) throws Exception {
        List<String> lines = Files.readAllLines(file);
        Properties props = new Properties();
        for (String line : lines) {
            Matcher m = PROP_LINE.matcher(line);
            if (m.matches()) {
                props.put(m.group(1), m.group(2));
            } else {
                break;
            }
        }

        if ("true".equals(props.get("ignore"))
                || IGNORE_BROKEN && "true".equals(props.get("broken"))) {
            Assumptions.abort("This test case has been marked to be ignored");
        }

        props.keySet().stream().filter(k -> !SUPPORTED_KEYS.contains(k)).forEach(
            k -> fail("Unsupported test spec key: " + k));

        try {
            tryLoadFile(file);
            // No exception encountered
            assertEquals("true", props.getProperty("noException"),
                "Unless 'noException: true' has been set, an exception is expected");

        } catch (Error ae) {
            throw ae;
        } catch (Throwable e) {
            Throwable error = e;
            if (error instanceof ProblemLoaderException) {
                error = error.getCause();
            }
            if ("true".equals(props.getProperty("verbose"))) {
                LOGGER.info("Exception raised while parsing {}", file.getFileName(), error);
            }

            try {
                assertNotEquals("true", props.getProperty("noException"),
                    "'noException: true' has been set: no exception expected");

                // We must use throwable here since there are some Errors around ...
                String exc = props.getProperty("exceptionClass");
                if (exc != null) {
                    if (exc.contains(".")) {
                        assertEquals(exc, error.getClass().getName(), "Exception type expected");
                    } else {
                        assertEquals(exc, error.getClass().getSimpleName(),
                            "Exception type expected");
                    }
                }

                String actualMessage = ExceptionTools.getMessage(error);
                String msg = props.getProperty("msgContains");
                String errMsg = e.getMessage();
                if (msg != null) {
                    assertTrue(actualMessage.contains(msg),
                        "Message must contain '" + msg + "', but message is: '" + actualMessage
                            + "'");
                }

                msg = props.getProperty("msgMatches");
                if (msg != null) {
                    assertTrue(actualMessage.matches(msg),
                        "Message must match regular expression '" + msg + "', but is '"
                            + actualMessage + "'");
                }

                msg = props.getProperty("msgIs");
                if (msg != null) {
                    assertEquals(msg, actualMessage,
                        "Message must be " + msg + ", but is " + actualMessage + "'");
                }

                String loc = props.getProperty("position");
                if (loc != null) {
                    Location actLoc = ExceptionTools.getLocation(error);
                    if (actLoc == null) {
                        throw new Exception("there is no location in the exception");
                    }
                    assertEquals(file.toUri(), actLoc.getFileURI().orElse(null),
                        "Exception location must point to file under test");
                    assertEquals(loc, actLoc.getPosition().toString());
                }

                if ("true".equals(props.getProperty("broken"))) {
                    LOGGER.warn(
                        "This test case is marked as broken, but it would actually succeed!");
                }

            } catch (AssertionFailedError assertionFailedError) {
                // in case of a failed assertion log the stacktrace
                LOGGER.info("Original stacktrace leading to failed junit assertion in {}",
                    file.getFileName(), error);
                // e.printStackTrace();
                throw assertionFailedError;
            }
        }
    }


}
