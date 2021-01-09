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
import org.jetbrains.annotations.NotNull;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
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

@RunWith(Parameterized.class)
public class MasterHandlerTest {

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

        int i = 1;
        while(props.containsKey("contains." + i)) {
            assertThat("Occurrence check",
                    translation,
                    StringContains.containsString(props.get("contains." + i).trim()));
            i++;
        }

        this.translation = translation;
    }

    @Before
    public void makeTranslation() throws IOException, ProblemLoaderException {
        BufferedReader reader = Files.newBufferedReader(path);
        this.props = new LineProperties();
        props.read(reader);

        Path tmpKey = Files.createTempFile("SMT_key_test", ".key");
        Files.write(tmpKey, props.getLines("KeY"));

        KeYEnvironment<DefaultUserInterfaceControl> env =
                KeYEnvironment.load(tmpKey.toFile());

        Proof proof = env.getLoadedProof();
        Sequent sequent = proof.root().sequent();

        SMTSettings settings = new SMTSettings(
                proof.getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
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
        Process proc = new ProcessBuilder("z3", "-in", "-T:5").start();
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
                    fail("Unexpected expecataion: " + expectation);
            }

            for (String line : response) {
                if (line.startsWith("(error ")) {
                    fail("An error in Z3: " + line);
                }
                if (lookFor != null && line.equals(lookFor)) {
                    return;
                }
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