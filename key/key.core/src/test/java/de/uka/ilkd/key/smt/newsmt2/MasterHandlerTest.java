package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.util.LineProperties;
import org.hamcrest.core.StringContains;
import org.junit.Assume;
import org.junit.Before;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.MethodSorters;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.key_project.util.Streams;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStream;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;

import static org.junit.Assert.*;

/**
 * Run this with
 * <pre>
 *     gradlew :key.core:testStrictSMT
 * </pre>
 */

@RunWith(Parameterized.class)
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class MasterHandlerTest {

    /**
     * If this variable is set when running this test class, then
     * those cases with expected result "weak_valid" will raise an
     * exception unless they can be proved using the solver.
     *
     * Otherwise a "timeout" or "unknown" is accepted. This can be
     * used to deal with test cases that should verify but do not
     * yet do so.
     *
     * (Default false)
     */
    private static final boolean STRICT_TEST =
            Boolean.getBoolean("key.newsmt2.stricttests");

    private static final boolean DUMP_SMT = true;

    @Parameter(0)
    public String name;

    @Parameter(1)
    public Path path;

    private String translation;

    private LineProperties props;

    @Parameters(name = "{0}")
    public static List<Object[]> data() throws IOException, URISyntaxException {

        URL url = MasterHandlerTest.class.getResource("cases");
        if (url == null) {
            throw new FileNotFoundException("Cannot find resource 'cases'.");
        }

        if (!url.getProtocol().equals("file")) {
            throw new IOException("Resource should be a file URL not " + url);
        }

        Path directory = Paths.get(url.toURI());
        assertTrue(Files.isDirectory(directory));

        List<Object[]> result = new ArrayList<>();
        Files.list(directory).forEach(f -> {
            Object[] item = { f.getFileName().toString(), f };
            result.add(item);
        });

        return result;
    }

    @Test
    public void testTranslation() throws Exception {

        if(DUMP_SMT) {
            Path tmpSmt = Files.createTempFile("SMT_key_" + name, ".smt2");
            // FIXME This is beyond Java 8: add as soon as switched to Java 11:
            // Files.writeString(tmpSmt, translation);
            Files.write(tmpSmt, translation.getBytes());
            System.err.println("SMT2 for " + name + " saved in: " + tmpSmt);
        }

        int i = 1;
        while(props.containsKey("contains." + i)) {
            assertThat("Occurrence check for contains." + i,
                    translation,
                    new ContainsModuloSpaces(props.get("contains." + i).trim()));
            i++;
        }

    }

    @Before
    public void makeTranslation() throws IOException, ProblemLoaderException {

        BufferedReader reader = Files.newBufferedReader(path);
        this.props = new LineProperties();
        props.read(reader);

        Assume.assumeFalse("Test case has been marked ignore",
                "ignore".equals(props.get("state")));

        List<String> sources = props.getLines("sources");
        List<String> lines = new ArrayList<>(props.getLines("KeY"));

        if (!sources.isEmpty()) {
            Path srcDir = Files.createTempDirectory("SMT_key_" + name);
            Path tmpSrc = srcDir.resolve("src.java");
            Files.write(tmpSrc, sources);
            lines.add(0, "\\javaSource \"" + srcDir + "\";\n");
        }

        Path tmpKey = Files.createTempFile("SMT_key_" + name, ".key");
        Files.write(tmpKey, lines);

        KeYEnvironment<DefaultUserInterfaceControl> env =
                KeYEnvironment.load(tmpKey.toFile());

        Proof proof = env.getLoadedProof();
        Sequent sequent = proof.root().sequent();

        SMTSettings settings = new SMTSettings(
                proof.getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                proof.getSettings().getNewSMTSettings(),
                proof);

        ModularSMTLib2Translator translator = new ModularSMTLib2Translator();
        this.translation =
                translator.translateProblem(sequent, env.getServices(), settings).toString();
    }

    @Test
    public void testZ3() throws Exception {

        String expectation = props.get("expected");
        Assume.assumeTrue("No Z3 expectation.", expectation != null);
        expectation = expectation.toLowerCase().trim();

        // TODO Run Z3 on the SMT translation
        // FIXME This is a hack.
        Process proc = new ProcessBuilder("z3", "-in", "-smt2", "-T:5").start();
        OutputStream os = proc.getOutputStream();
        os.write(translation.getBytes());
        os.write("\n\n(check-sat)".getBytes());
        os.close();

        String[] response = Streams.toString(proc.getInputStream()).split("\n");

        try {
            String lookFor = null;
            switch (expectation) {
                case "valid":
                    lookFor = "unsat";
                    break;
                case "fail":
                    lookFor = "sat";
                    break;
                case "irrelevant":
                    break;
                default:
                    fail("Unexpected expectation: " + expectation);
            }

            for (String line : response) {
                if (line.startsWith("(error ")) {
                    fail("An error in Z3: " + line);
                }
                if (lookFor != null && line.equals(lookFor)) {
                    return;
                }
            }

            if(!STRICT_TEST) {
                Assume.assumeFalse("This is an extended test (will be run only in strict mode)",
                        "extended".equals(props.get("state")));
            }

            if (lookFor != null) {
                fail("Expectation not found");
            }
        } catch(Throwable t) {
            System.out.println("Z3 input");
            System.out.println(translation);

            System.out.println("\n\nZ3 response");
            for (String s : response) {
                System.out.println(s);
            }
            throw t;
        }
    }

}