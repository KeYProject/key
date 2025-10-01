package de.uka.ilkd.key.scripts;

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

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.Comparator;
import java.util.stream.Stream;

public class JmlScriptTest {

    private static final Path KEY_FILE;
    static {
        URL url = JmlScriptTest.class.getResource("jml/project.key");
        try {
            KEY_FILE = Paths.get(url.toURI());
        } catch (URISyntaxException e) {
            throw new RuntimeException(e);
        }
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("filesProvider")
    public void testJmlScript(Path path) throws Exception {

        Path tmpDir = Files.createTempDirectory("key.jmltest.");
        try {
            Files.copy(path, tmpDir.resolve("Test.java"));
            Path projectFile = tmpDir.resolve("project.key");
            Files.copy(KEY_FILE, projectFile);
            KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(projectFile);
            KeyAst.ProofScript script = env.getProofScript();
            if (script != null) {
                ProofScriptEngine pse = new ProofScriptEngine(script);
                pse.execute(env.getUi(), env.getLoadedProof());
            }
            // TODO read comments from java file to allow for more than only closed proofs ...
            Assertions.assertTrue(env.getLoadedProof().closed(), "Proof did not close.");
        } finally {
            // Uncomment the following line to delete the temporary directory after the test
            // Files.walk(tmpDir).sorted(Comparator.reverseOrder()).map(Path::toFile).forEach(File::delete);
        }

    }

    public static Stream<Arguments> filesProvider() throws URISyntaxException, IOException {
        URL jmlUrl = JmlScriptTest.class.getResource("jml");
        return Files.list(Paths.get(jmlUrl.toURI()))
                .filter(p -> p.toString().endsWith(".java"))
                .map(p -> Arguments.of(p));
    }



}
