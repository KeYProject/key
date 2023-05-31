package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
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

import static org.junit.jupiter.api.Assertions.*;

/**
 * @author Mattias Ulbrich
 */
public class JMLParserExceptionTest {

    public static final boolean IGNORE_BROKEN = true;

    private final static Pattern PROP_LINE = Pattern.compile("// *(\\p{Alnum}+) *[:=] *(.*)");

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

        if("true".equals(props.get("ignore")) || IGNORE_BROKEN && "true".equals(props.get("broken"))) {
            Assumptions.abort("This test case has been marked to be ignored");
        }

        try {
            ProblemLoaderControl control = new DefaultUserInterfaceControl(null);
            AbstractProblemLoader pl = new SingleThreadProblemLoader(file.toFile(), null, null, null, AbstractProfile.getDefaultProfile(), false,
                    control, false, new Properties());
            pl.setLoadSingleJavaFile(true);
            pl.load();
            // No exception encountered
            assertEquals("true", props.get("noException"), "Unless 'noException: true' has been set, an exception is expected");

        } catch (Throwable e) {
            if("true".equals(props.getProperty("verbose"))) {
                e.printStackTrace();
            }

            // We must use throwable here since there are some Errors around ...
            String exc = props.getProperty("exceptionClass");
            if (exc != null) {
                if(exc.contains(".")) {
                    assertEquals(exc, e.getClass().getName(), "Exception type expected");
                } else {
                    assertEquals(exc, e.getClass().getSimpleName(), "Exception type expected");
                }
            }

            String msg = props.getProperty("msgContains");
            if(msg != null) {
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
                assertEquals(file.toUri().toURL(), actLoc.getFileURL(), "Exception location must point to file under test");
                assertEquals(loc, actLoc.getPosition().toString());
            }
        }
    }
}
