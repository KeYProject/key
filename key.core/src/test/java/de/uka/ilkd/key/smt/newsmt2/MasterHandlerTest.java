/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStream;
import java.io.StringReader;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import java.util.stream.Collectors;
import javax.annotation.Nullable;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.util.LineProperties;

import org.key_project.util.Streams;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

/**
 * Run this with
 *
 * <pre>
 *     gradlew :key.core:testStrictSMT
 * </pre>
 */
public class MasterHandlerTest {
    /**
     * If this variable is set when running this test class, then those cases with expected result
     * "weak_valid" will raise an exception unless they can be proved using the solver.
     * <p>
     * Otherwise a "timeout" or "unknown" is accepted. This can be used to deal with test cases that
     * should verify but do not yet do so.
     * <p>
     * (Default false)
     */
    private static final boolean STRICT_TEST = Boolean.getBoolean("key.newsmt2.stricttests");
    private static final boolean DUMP_SMT = true;
    private static final Logger LOGGER = LoggerFactory.getLogger(MasterHandlerTest.class);
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3 (Legacy Translation)"))
            .findFirst().orElse(null);

    public static List<Arguments> data()
            throws IOException, URISyntaxException, ProblemLoaderException {
        URL url = MasterHandlerTest.class.getResource("cases");
        if (url == null) {
            throw new FileNotFoundException("Cannot find resource 'cases'.");
        }

        if (!url.getProtocol().equals("file")) {
            throw new IOException("Resource should be a file URL not " + url);
        }

        Path directory = Paths.get(url.toURI());
        Assertions.assertTrue(Files.isDirectory(directory));

        List<Path> files;
        try (var s = Files.list(directory)) {
            files = s.collect(Collectors.toList());
        }
        List<Arguments> result = new ArrayList<>(files.size());
        for (Path file : files) {
            try {
                final var testData = TestData.create(file);
                if (testData != null) {
                    result.add(Arguments.of(testData));
                }
            } catch (Exception e) {
                LOGGER.error("Error reading {}", file, e);
            }
        }
        return result;
    }

    public static class TestData {
        public final String name;
        public final Path path;
        private final String translation;
        private final LineProperties props;

        public TestData(String name, Path path, LineProperties props, String translation) {
            this.name = name;
            this.path = path;
            this.translation = translation;
            this.props = props;
        }

        @Nullable
        public static TestData create(Path path) throws IOException, ProblemLoaderException {
            var name = path.getFileName().toString();
            var props = new LineProperties();
            try (BufferedReader reader = Files.newBufferedReader(path)) {
                props.read(reader);
            }

            if ("ignore".equals(props.get("state"))) {
                LOGGER.info("Test case has been marked ignore");
                return null;
            }

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

            KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(tmpKey.toFile());

            Proof proof = env.getLoadedProof();
            Sequent sequent = proof.root().sequent();

            SMTSettings settings = new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                proof.getSettings().getNewSMTSettings(), proof);

            String updates = props.get("smt-settings");
            if (updates != null) {
                Properties map = new Properties();
                map.load(new StringReader(updates));
                settings.getNewSettings().readSettings(map);
            }

            ModularSMTLib2Translator translator = new ModularSMTLib2Translator();
            var translation =
                translator.translateProblem(sequent, env.getServices(), settings).toString();
            return new TestData(name, path, props, translation);
        }

        @Override
        public String toString() {
            return name;
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    public void testTranslation(TestData data) throws Exception {
        if (DUMP_SMT) {
            Path tmpSmt = Files.createTempFile("SMT_key_" + data.name, ".smt2");
            // FIXME This is beyond Java 8: add as soon as switched to Java 11:
            // Files.writeString(tmpSmt, translation);
            Files.write(tmpSmt, data.translation.getBytes(StandardCharsets.UTF_8));
            LOGGER.info("SMT2 for {}  saved in: {}", data.name, tmpSmt);
        }

        int i = 1;
        while (data.props.containsKey("contains." + i)) {
            assertTrue(
                containsModuloSpaces(data.translation, data.props.get("contains." + i).trim()),
                "Occurrence check for contains." + i);
            i++;
        }

    }

    public static boolean containsModuloSpaces(String haystack, String needle) {
        String n = needle.replaceAll("\\s+", " ");
        String h = haystack.replaceAll("\\s+", " ");
        return h.contains(n);
    }


    @ParameterizedTest
    @MethodSource("data")
    public void testZ3(TestData data) throws Exception {
        Assumptions.assumeTrue(Z3_SOLVER != null);
        Assumptions.assumeTrue(Z3_SOLVER.isInstalled(false),
            "Z3 is not installed, this testcase is ignored.");

        String expectation = data.props.get("expected");
        Assumptions.assumeTrue(expectation != null, "No Z3 expectation.");
        expectation = expectation.toLowerCase().trim();

        // TODO Run Z3 on the SMT translation
        // FIXME This is a hack.
        Process proc = new ProcessBuilder("z3", "-in", "-smt2", "-T:5").start();
        OutputStream os = proc.getOutputStream();
        os.write(data.translation.getBytes(StandardCharsets.UTF_8));
        os.write("\n\n(check-sat)".getBytes(StandardCharsets.UTF_8));
        os.close();

        String[] response = Streams.toString(proc.getInputStream()).split(System.lineSeparator());

        try {
            String lookFor = null;
            switch (expectation) {
            case "valid":
                lookFor = "unsat";
                break;
            case "fail":
                lookFor = "(sat|timeout)";
                break;
            case "irrelevant":
                break;
            default:
                fail("Unexpected expectation: " + expectation);
            }

            if (lookFor != null) {
                for (String line : response) {
                    if (line.startsWith("(error ")) {
                        fail("An error in Z3: " + line);
                    }
                    if (line.matches(lookFor)) {
                        return;
                    }
                }
            }

            if (!STRICT_TEST) {
                assumeFalse("extended".equals(data.props.get("state")),
                    "This is an extended test (will be run only in strict mode)");
            }

            if (lookFor != null) {
                fail("Expectation not found");
            }
        } catch (Throwable t) {
            LOGGER.error("Z3 input {}", data.translation);
            LOGGER.error("Z3 response: {}", response, t);
            throw t;
        }
    }

}
