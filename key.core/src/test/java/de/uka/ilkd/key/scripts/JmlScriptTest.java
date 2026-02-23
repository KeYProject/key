/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.KeYConstants;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class JmlScriptTest {

    private static final Path KEY_FILE;
    private static final Logger LOGGER = LoggerFactory.getLogger(JmlScriptTest.class);

    // Set this to a specific case to only run that case for debugging
    private static final String ONLY_CASE = System.getProperty("key.testJmlScript.only");
    // Set this to true to save the proof after running the script
    private static final boolean SAVE_PROOF = false;

    static {
        URL url = JmlScriptTest.class.getResource("jml/project.key");
        try {
            KEY_FILE = Paths.get(url.toURI());
        } catch (URISyntaxException e) {
            throw new RuntimeException(e);
        }
    }

    @ParameterizedTest(name = "{1}")
    @MethodSource("filesProvider")
    public void testJmlScript(Path path, String identifier) throws Exception {

        Parameters params = readParams(path);

        Path tmpDir = Files.createTempDirectory("key.jmltest.");
        try {
            Files.copy(path, tmpDir.resolve("Test.java"));
            Path projectFile = tmpDir.resolve("project.key");
            Files.copy(KEY_FILE, projectFile);
            KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(projectFile);
            if (params.settings != null && !params.settings.isEmpty()) {
                for (Map.Entry<String, String> entry : params.settings.entrySet()) {
                    env.getLoadedProof().getSettings().getStrategySettings()
                            .getActiveStrategyProperties()
                            .setProperty(entry.getKey(), entry.getValue());
                }
            }
            KeyAst.ProofScript script = env.getProofScript();
            if (script != null) {
                ProofScriptEngine pse = new ProofScriptEngine(env.getLoadedProof());
                pse.execute(env.getUi(), script);
            }

            if (SAVE_PROOF) {
                String filename = tmpDir.resolve("saved.proof").toString();
                ProofSaver saver =
                    new ProofSaver(env.getLoadedProof(), filename, KeYConstants.INTERNAL_VERSION);
                saver.save();
                LOGGER.info("Saved proof to {}", filename);
            }

            if (params.shouldClose) {
                Assertions.assertTrue(env.getLoadedProof().closed(), "Proof did not close.");
            } else {
                Assertions.assertFalse(env.getLoadedProof().closed(), "Proof closes unexpectedly.");
            }
        } finally {
            // Uncomment the following line to delete the temporary directory after the test
            if (params.deleteTmpDir && !SAVE_PROOF) {
                LOGGER.info("Deleting temporary directory: {}", tmpDir);
                Files.walk(tmpDir).sorted(Comparator.reverseOrder()).map(Path::toFile)
                        .forEach(File::delete);
            } else {
                LOGGER.info("Temporary directory retained for inspection: {}", tmpDir);
            }
        }

    }

    private static Parameters readParams(Path path) throws IOException {
        String input = Files.lines(path).filter(l -> l.startsWith("//!")).map(l -> l.substring(3))
                .collect(Collectors.joining("\n")).trim();
        if (input.isEmpty()) {
            return new Parameters();
        }
        var objectMapper = new ObjectMapper(new YAMLFactory());
        objectMapper.findAndRegisterModules();
        return objectMapper.readValue(input, Parameters.class);
    }

    public static Stream<Arguments> filesProvider() throws URISyntaxException, IOException {
        URL jmlUrl = JmlScriptTest.class.getResource("jml");
        if (ONLY_CASE != null) {
            return Stream.of(Arguments.of(Paths.get(jmlUrl.toURI()).resolve(ONLY_CASE),
                "single specified case: " + ONLY_CASE));
        } else {
            return Files.list(Paths.get(jmlUrl.toURI()))
                    .filter(p -> p.toString().endsWith(".java"))
                    .map(p -> Arguments.of(p, p.getFileName().toString()));
        }
    }

    static class Parameters {
        public boolean shouldClose = true;
        public String method;
        public String exception;
        public boolean deleteTmpDir = true;
        public Map<String, String> settings;
    }


}
