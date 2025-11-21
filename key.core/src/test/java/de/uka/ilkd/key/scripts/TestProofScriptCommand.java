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
import de.uka.ilkd.key.nparser.ParsingFacade;
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

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * see {@link MasterHandlerTest} from where I copied quite a bit.
 */
public class TestProofScriptCommand {
    public record TestInstance(
            String name,
            String key, String script, @Nullable String exception,
            String[] goals, Integer selectedGoal) {
    }

    public static List<Arguments> data() throws IOException, URISyntaxException {
        var folder = Paths.get("src/test/resources/de/uka/ilkd/key/scripts/cases")
                .toAbsolutePath();
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
                    args.add(Arguments.of(instance));
                } catch (Exception e) {
                    System.out.println(path);
                    e.printStackTrace();
                    throw e;
                }
            }
            return args;
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    void testProofScript(TestInstance data) throws Exception {
        var name = data.name();
        Path tmpKey = Files.createTempFile("proofscript_key_" + name, ".key");
        Files.writeString(tmpKey, data.key());

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(tmpKey);

        Proof proof = env.getLoadedProof();

        var script = ParsingFacade.parseScript(data.script());
        ProofScriptEngine pse = new ProofScriptEngine(script);

        boolean hasException = data.exception() != null;
        try {
            pse.execute(env.getUi(), proof);
        } catch (ScriptException ex) {
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
                assertThat(goals.head().toString().trim()).isEqualTo(expectedGoal);
                goals = goals.tail();
            }

            if (data.selectedGoal() != null) {
                Goal goal = pse.getStateMap().getFirstOpenAutomaticGoal();
                assertThat(goal.toString().trim()).isEqualTo(data.goals()[data.selectedGoal()]);
            }
        }
    }

}
