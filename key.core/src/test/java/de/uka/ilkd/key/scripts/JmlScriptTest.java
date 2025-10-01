package de.uka.ilkd.key.scripts;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.util.Debug;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.logging.LogManager;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class JmlScriptTest {

    private static final Path KEY_FILE;
    private static final Logger LOGGER = LoggerFactory.getLogger(JmlScriptTest.class);

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
            KeyAst.ProofScript script = env.getProofScript();
            if (script != null) {
                ProofScriptEngine pse = new ProofScriptEngine(env.getLoadedProof());
                pse.execute(env.getUi(), script);
            }

            if(params.shouldClose) {
                Assertions.assertTrue(env.getLoadedProof().closed(), "Proof did not close.");
            } else {
                Assertions.assertFalse(env.getLoadedProof().closed(), "Proof closes unexpectedly.");
            }
        } finally {
            // Uncomment the following line to delete the temporary directory after the test
            if(params.deleteTmpDir) {
                LOGGER.info("Deleting temporary directory: {}", tmpDir);
                Files.walk(tmpDir).sorted(Comparator.reverseOrder()).map(Path::toFile).forEach(File::delete);
            } else {
                LOGGER.info("Temporary directory retained for inspection: {}", tmpDir);
            }
        }

    }

    private static Parameters readParams(Path path) throws IOException {
        String input = Files.lines(path).filter(l -> l.startsWith("//!")).map(l -> l.substring(3).trim())
                        .collect(Collectors.joining("\n")).trim();
        if(input.isEmpty()) {
            return new Parameters();
        }
        var objectMapper = new ObjectMapper(new YAMLFactory());
        objectMapper.findAndRegisterModules();
        return objectMapper.readValue(input, Parameters.class);
    }

    public static Stream<Arguments> filesProvider() throws URISyntaxException, IOException {
        URL jmlUrl = JmlScriptTest.class.getResource("jml");
        return Files.list(Paths.get(jmlUrl.toURI()))
                .filter(p -> p.toString().endsWith(".java"))
                .map(p -> Arguments.of(p, p.getFileName().toString()));
    }

    static class Parameters {
        public boolean shouldClose = true;
        public String method;
        public String exception;
        public boolean deleteTmpDir = true;
    }


}
