package de.uka.ilkd.key.speclang.njml;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.util.ExceptionTools;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.opentest4j.AssertionFailedError;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This test case is used to ensure that errors in JML (and perhaps also in Java)
 * are reported with a reasonable error message and the right position pointing
 * into the file.
 *
 * To add a test case, locate the "exceptional" directory in the resources
 * (below the directory for this package here) and add your single Java file
 * that contains an error that should be presented to the user (like syntax
 * error, unresolved names, ...)
 *
 * The first lines of the Java file may contain meta data on what to expect
 * from the exception. Meta data are key-value pairs like
 *
 * <pre>
 * // &lt;key&gt;: &lt;value&gt;
 * </pre>
 *
 * The following keys are supported
 * <table>
 * <tr>
 * <th>Key</th>
 * <th>Description</th>
 * </tr>
 * <tr>
 * <td>{@code noException}</td>
 * <td>This particular file must
 * <b>not</b> throw an exception. Default: false</td>
 * </tr>
 * <tr>
 * <td>{@code exceptionClass}</td>
 * <td>Either a fully qualified class name or
 * a short classname (w/o package prefix) of the actual type of the
 * exception. Optional.</td>
 * </tr>
 * <tr>
 * <td>{@code msgContains}</td>
 * <td>A string which occur somewhere in the
 * exception message (obtained via {@link Exception#getMessage()}). Optional</td>
 * </tr>
 * <tr>
 * <td>{@code msgMatches}</td>
 * <td>A regular expression that must match the exception message (obtained via
 * {@link Exception#getMessage()}). Optional</td>
 * </tr>
 * <tr>
 * <td>{@code msgIs}</td>
 * <td>A string to which the exception message (obtained via {@link Exception#getMessage()}) must be
 * equal. Optional</td>
 * </tr>
 * <tr>
 * <td>{@code position}</td>
 * <td>A tuple in form {@code <line>/<col>} describing the position within this file. Both line and
 * column are 1-based.
 * It is also checked that the URL of the location points to the file under test. Optional</td>
 * </tr>
 * <tr>
 * <td>{@code ignore}</td>
 * <td>Ignore this test case if set to true. Default is false.</td>
 * </tr>
 * <tr>
 * <td>{@code broken}</td>
 * <td>If broken tests are disabled, ignore this test case if set to true. Indicates that this needs
 * to be fixed! Default is false.</td>
 * </tr>
 * <tr>
 * <td>{@code verbose}</td>
 * <td>Print the stacktrace if set to true. Default is false.</td>
 * </tr>
 * </table>
 *
 *
 * @author Mattias Ulbrich
 */
public class JMLParserExceptionTest {

    public static final boolean IGNORE_BROKEN = true;

    private final static Pattern PROP_LINE =
        Pattern.compile("//\\s*(\\p{Alnum}+)\\s*[:=]\\s*(.*?)\\s*");

    public static Stream<Arguments> getFiles() throws URISyntaxException, IOException {
        URL fileURL = JMLParserExceptionTest.class.getResource("exceptional");
        assert fileURL != null : "Directory 'exceptional' not found";
        assert fileURL.getProtocol().equals("file") : "Test resources must be in file system";
        Path dir = Paths.get(fileURL.toURI());
        return Files.list(dir).map(it -> Arguments.of(it, it.getFileName()));
    }

    @ParameterizedTest(name = "case {1}")
    @MethodSource("getFiles")
    public void testParseAndInterpret(Path file, Path localFilename) throws Exception {
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

        try {
            ProblemLoaderControl control = new DefaultUserInterfaceControl(null);
            AbstractProblemLoader pl = new SingleThreadProblemLoader(file.toFile(), null, null,
                null, AbstractProfile.getDefaultProfile(), false,
                control, false, new Properties());
            pl.setLoadSingleJavaFile(true);
            pl.load();
            // No exception encountered
            assertEquals("true", props.get("noException"),
                "Unless 'noException: true' has been set, an exception is expected");

        } catch (Throwable e) {
            if ("true".equals(props.getProperty("verbose"))) {
                e.printStackTrace();
            }

            try {
                assertNotEquals("true", props.get("noException"),
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
                if (msg != null) {
                    assertTrue(e.getMessage().contains(msg));
                }

                msg = props.getProperty("msgMatches");
                if (msg != null) {
                    assertTrue(e.getMessage().matches(msg));
                }

                msg = props.getProperty("msgIs");
                if (msg != null) {
                    assertEquals(msg, e.getMessage());
                }

                String loc = props.getProperty("position");
                if (loc != null) {
                    Location actLoc = ExceptionTools.getLocation(e);
                    assertNotNull(actLoc, "Exception location must not be null");
                    assertEquals(file.toUri().toURL(), actLoc.getFileURL(),
                        "Exception location must point to file under test");
                    assertEquals(loc, actLoc.getPosition().toString());
                }
            } catch (AssertionFailedError assertionFailedError) {
                // in case of a failed assertion print the stacktrace
                System.err.println("Original stacktrace:");
                e.printStackTrace();
                throw assertionFailedError;
            }
        }
    }
}
