/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.newsmt2.MasterHandlerTest;

import org.key_project.util.collection.ImmutableList;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * see {@link MasterHandlerTest} from where I copied quite a bit.
 */
public class TestProofScriptCommand {

    private static final String ONLY_CASE = null;
    private static final Logger LOGGER = LoggerFactory.getLogger(TestProofScriptCommand.class);

    public record TestInstance(
            String name,
            String key,
            String script,
            @Nullable String exception,
            String[] goals,
            Integer selectedGoal) {
    }

    public static List<Arguments> data() throws IOException, URISyntaxException {
        var folder = Paths.get("src/test/resources/de/uka/ilkd/key/scripts/cases")
                .toAbsolutePath();

        if(ONLY_CASE != null) {
             folder = folder.resolve(ONLY_CASE);
        }

        try (var walker = Files.walk(folder)) {
            List<Path> files =
                walker.filter(it -> it.getFileName().toString().endsWith(".yml")).toList();
            var objectMapper = new ObjectMapper(new YAMLFactory());
            objectMapper.findAndRegisterModules();

            List<Arguments> args = new ArrayList<>(files.size());
            for (Path path : files) {
                try {
                    TestInstance instance =
                        objectMapper.readValue(path.toFile(), TestInstance.class);
                    var name = instance.name == null ?
                            path.getFileName().toString().substring(0, path.getFileName().toString().length() - 4) :
                            instance.name;
                    args.add(Arguments.of(instance, name));
                } catch (Exception e) {
                    System.out.println(path);
                    e.printStackTrace();
                    throw e;
                }
            }
            return args;
        }
    }

    @ParameterizedTest(name = "{1}")
    @MethodSource("data")
    void testProofScript(TestInstance data, String name) throws Exception {
        Path tmpKey = Files.createTempFile("proofscript_key_" + name, ".key");
        LOGGER.info("Testing {} using file", name, tmpKey);
        Files.writeString(tmpKey, data.key());

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(tmpKey);

        Proof proof = env.getLoadedProof();

        KeyAst.ProofScript script = ParsingFacade.parseScript(data.script());
        ProofScriptEngine pse = new ProofScriptEngine(proof);

        boolean hasException = data.exception() != null;
        try {
            pse.execute(env.getUi(), script);
        } catch (ScriptException ex) {
            ex.printStackTrace();
            assertTrue(data.exception != null && !data.exception.isEmpty(),
                "An exception was not expected, but got " + ex.getMessage());
            // weigl: fix spurious error on Windows machine due to different file endings.
            String msg = ex.getMessage().trim().replaceAll("\r\n", "\n");
            assertThat(msg)
                    .containsIgnoringWhitespaces(data.exception.trim())
                    .as("Unexpected exception: %s\n expected: %s",
                        ex.getMessage(), data.exception.trim());
            return;
        }

        Assertions.assertFalse(hasException,
            "exception would have been expected");

        if (data.goals() != null) {
            ImmutableList<Goal> goals = proof.openGoals();
            int expected = data.goals().length;
            Assertions.assertEquals(expected, goals.size());

            for (String expectedGoal : data.goals()) {
                assertThat(normaliseSpace(goals.head().toString())).isEqualTo(expectedGoal);
                goals = goals.tail();
            }

            if (data.selectedGoal() != null) {
                Goal goal = pse.getStateMap().getFirstOpenAutomaticGoal();
                assertThat(normaliseSpace(goal.toString())).isEqualTo(data.goals()[data.selectedGoal()]);
            }
        }
    }

    // For some layout reasons the toString may add linebreaks and spaces
    private static String normaliseSpace(String str) {
        return str.replaceAll("\\s+", " ").trim();
    }

}
