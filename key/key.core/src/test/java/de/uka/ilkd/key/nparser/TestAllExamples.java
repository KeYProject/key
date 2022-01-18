package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.nparser.builder.ProblemFinder;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.key_project.util.helper.FindResources;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Alexander Weigl
 * @version 1 (13.09.19)
 */
@Tag("interactive")
public class TestAllExamples {
    public static Stream<Path> getFiles() throws IOException {
        File examples = FindResources.findFolder("key.ui/examples", "../key.ui/examples");
        Assumptions.assumeTrue(examples != null);
        return Files.walk(examples.toPath())
                .filter(f -> Files.isRegularFile(f) && f.getFileName().endsWith(".key"));
    }

    @ParameterizedTest
    @MethodSource("getFiles")
    @Disabled("Not all files are parseable without Java Type support. ")
    public void parse(Path file) throws IOException {
        KeyIO io = getIo();
        ProblemFinder o = io.load(file).loadCompleteProblem();
        System.out.println(o);
        assertTrue(o.getProblemTerm() != null || o.getChooseContract() != null || o.getProofObligation() != null);
    }

    private KeyIO getIo() throws IOException {
        URL u = getClass().getResource("/de/uka/ilkd/key/proof/rules/standardRules.key");
        KeyIO io = new KeyIO();
        io.load(u).loadComplete();
        io.getServices().getTypeConverter().init();
        return io;
    }
}

