/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

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
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.ExceptionTools;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.opentest4j.AssertionFailedError;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This test case is used to ensure that errors in KeY files are reported
 * with a reasonable error message and the right position pointing
 * into the file.
 *
 * To add a test case, locate the "exceptional" directory in the resources
 * (below the directory for this package here) and add a .key file
 * that contains an error that should be presented to the user (like syntax
 * error, unresolved names, ...)
 *
 * See README.md in said directory for information on the meta-data inside
 * the files.
 *
 * @author Mattias Ulbrich
 */
public class ParserExceptionTest {

    // The following can be changed temporarily to control run tests
    private static final boolean IGNORE_BROKEN = false;

    // File name local to the res directory with the test cases
    // Can be used for temporary debugging
    private static final String FIX_FILE = null; // "conflict.key";

    private static final Set<String> SUPPORTED_KEYS =
        Set.of("noException", "exceptionClass", "msgContains",
            "msgMatches", "msgIs", "position", "ignore", "broken", "verbose");

    private static final Logger LOGGER = LoggerFactory.getLogger(ParserExceptionTest.class);

    private final static Pattern PROP_LINE =
        Pattern.compile("//\\s*(\\p{Alnum}+)\\s*[:=]\\s*(.*?)\\s*");

    public static Stream<Arguments> getFiles() throws URISyntaxException, IOException {
        URL fileURL = ParserExceptionTest.class.getResource("exceptional");
        assert fileURL != null : "Directory 'exceptional' not found";
        assert fileURL.getProtocol().equals("file") : "Test resources must be in file system";
        Path dir = Paths.get(fileURL.toURI());
        if (FIX_FILE != null) {
            List<Arguments> list = List.of(Arguments.of(dir.resolve(FIX_FILE), FIX_FILE));
            return list.stream();
        }
        return Files.walk(dir).filter(it -> it.getFileName().toString().endsWith(".key"))
                .map(it -> Arguments.of(it, it.getFileName()));
    }


    @ParameterizedTest(name = "case {1}")
    @MethodSource("getFiles")
    public void testParseAndInterpret(Path file, Path localFilename) throws Exception {
        parseAndInterpret(file);
    }

    // This method does not depend on anything can also be called from other test cases.
    public static void parseAndInterpret(Path file) throws Exception {
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
            KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file.toFile());

            // No exception encountered
            assertEquals("true", props.getProperty("noException"),
                "Unless 'noException: true' has been set, an exception is expected");

            String checkScript = props.getProperty("checkScript");
            if (checkScript != null) {
                check(checkScript, env);
            }

        } catch (Error ae) {
            throw ae;
        } catch (Throwable e) {
            if ("true".equals(props.getProperty("verbose"))) {
                LOGGER.info("Exception raised while parsing {}", file.getFileName(), e);
            }

            try {
                assertNotEquals("true", props.getProperty("noException"),
                    "'noException: true' has been set: no exception expected");

                // We must use throwable here since there are some Errors around ...
                String exc = props.getProperty("exceptionClass");
                if (exc != null) {
                    if (exc.contains(".")) {
                        assertEquals(exc, e.getClass().getName(), "Exception type expected");
                    } else {
                        assertEquals(exc, e.getClass().getSimpleName(), "Exception type expected");
                    }
                }

                String msg = props.getProperty("msgContains");
                String errorMsg = e.getMessage();
                if (msg != null) {
                    assertNotNull(errorMsg);
                    assertTrue(errorMsg.contains(msg), "Message must contain " + msg);
                }

                msg = props.getProperty("msgMatches");
                if (msg != null) {
                    assertTrue(errorMsg.matches(msg),
                        "Message must match regular exp " + msg);
                }

                msg = props.getProperty("msgIs");
                if (msg != null) {
                    assertEquals(msg, errorMsg, "Message must be " + msg);
                }

                String loc = props.getProperty("position");
                if (loc != null) {
                    Location actLoc = ExceptionTools.getLocation(e).orElseThrow(
                        () -> new Exception("there is no location in the exception"));
                    assertEquals(file.toUri(), actLoc.getFileURI().orElse(null),
                        "Exception location must point to file under test");
                    assertEquals(loc, actLoc.getPosition().toString());
                }
            } catch (AssertionFailedError assertionFailedError) {
                // in case of a failed assertion log the stacktrace
                LOGGER.info("Original stacktrace leading to failed junit assertion in {}",
                    file.getFileName(), e);
                // e.printStackTrace();
                throw assertionFailedError;
            }
        }
    }

    /*
     * We can also provide some Java code to be checked on the resultung env object
     */
    private static void check(String checkScript, KeYEnvironment<DefaultUserInterfaceControl> env)
            throws ScriptException {
        ScriptEngine engine = new ScriptEngineManager().getEngineByName("java");
        engine.put("env", env);
        Object result = engine.eval(checkScript);
        assertEquals(Boolean.TRUE, result, "The checkscript failed and did not return true");
    }
}
