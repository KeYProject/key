/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
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
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.key_project.util.Streams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.OutputStream;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

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
     * Otherwise, a "timeout" or "unknown" is accepted. This can be used to deal with test cases
     * that
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
        try (var input = MasterHandlerTest.class.getResourceAsStream("cases.yml")) {
            var om = new ObjectMapper(new YAMLFactory());
            TypeReference<HashMap<String, TestData>> typeRef = new TypeReference<>() {
            };
            Map<String, TestData> preData = om.readValue(input, typeRef);
            var result = new ArrayList<Arguments>(preData.size());
            for (var entry : preData.entrySet()) {
                final var value = entry.getValue();

                if (value.state == TestDataState.IGNORE) {
                    LOGGER.info("Test {} case has been marked ignore", entry.getKey());
                    continue;
                }

                final var testData = value.load(entry.getKey());
                result.add(Arguments.of(testData));
            }
            return result;
        }
    }

    public enum TestDataState {
        EMPTY, EXTENDED, IGNORE
    }

    public enum Expectation {
        VALID, FAIL, IRRELEVANT
    }

    /**
     * This class contains the information about the test fixtures that is loaded via the YAML.
     * @param contains a list of strings that are expected in the SMT translation
     * @param smtSettings required key/values in the smt settings.
     * @param expected expected output of Z3
     * @param state    state of the test
     * @param javaSrc  path to necessary java sources
     * @param keySrc   contents of the key file to be loaded.
     */
    public record TestData(List<String> contains,
                           Properties smtSettings,
                           Expectation expected,
                           TestDataState state,
                           String javaSrc,
                           String keySrc
    ) {

        private LoadedTestData load(String name) throws IOException, ProblemLoaderException {
            var keySrc = keySrc();
            if (javaSrc != null && !javaSrc.isEmpty()) {
                Path srcDir = Files.createTempDirectory("SMT_key_" + name);
                Path tmpSrc = srcDir.resolve("src.java");
                Files.writeString(tmpSrc, javaSrc);
                keySrc += "\n\\javaSource \"%s\";\n".formatted(srcDir);
            }

            Path tmpKey = Files.createTempFile("SMT_key_%s".formatted(name), ".key");
            Files.writeString(tmpKey, keySrc);

            KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(tmpKey.toFile());

            Proof proof = env.getLoadedProof();
            Sequent sequent = proof.root().sequent();

            SMTSettings settings = new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                    proof.getSettings().getNewSMTSettings(), proof);

            if (smtSettings != null) {
                settings.getNewSettings().readSettings(smtSettings);
            }

            ModularSMTLib2Translator translator = new ModularSMTLib2Translator();
            var translation = translator.translateProblem(sequent, env.getServices(), settings).toString();
            return new LoadedTestData(name, this, translation);
        }
    }

    private record LoadedTestData(String name, TestData data, String translation) {
        @Override
        public String toString() {
            return name();
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    void testTranslation(LoadedTestData data) throws Exception {
        if (DUMP_SMT) {
            Path tmpSmt = Files.createTempFile("SMT_key_%s".formatted(data.name), ".smt2");
            Files.writeString(tmpSmt, data.translation);
            LOGGER.info("SMT2 for {}  saved in: {}", data.name, tmpSmt);
        }

        Assertions.assertThat(data.translation)
                .containsIgnoringWhitespaces(data.data.contains().toArray(new String[0]));
    }


    @ParameterizedTest
    @MethodSource("data")
    void testZ3(LoadedTestData data) throws Exception {
        Assumptions.assumeTrue(Z3_SOLVER != null);
        Assumptions.assumeTrue(Z3_SOLVER.isInstalled(false),
                "Z3 is not installed, this testcase is ignored.");

        var expectation = data.data.expected;
        Assumptions.assumeTrue(expectation != null, "No Z3 expectation.");

        // TODO Run Z3 on the SMT translation
        // FIXME This is a hack.
        Process proc = new ProcessBuilder("z3", "-in", "-smt2", "-T:5").start();
        OutputStream os = proc.getOutputStream();
        os.write(data.translation.getBytes(StandardCharsets.UTF_8));
        os.write("\n\n(check-sat)".getBytes(StandardCharsets.UTF_8));
        os.close();

        String[] response = Streams.toString(proc.getInputStream()).split(System.lineSeparator());

        try {
            String lookFor = switch (expectation) {
                case VALID -> "unsat";
                case FAIL -> "(sat|timeout)";
                case IRRELEVANT -> null;
            };

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
                assumeFalse(data.data.state == TestDataState.EXTENDED,
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
