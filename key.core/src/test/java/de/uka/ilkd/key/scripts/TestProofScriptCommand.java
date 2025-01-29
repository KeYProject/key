/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.newsmt2.MasterHandlerTest;

import org.key_project.util.collection.ImmutableList;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
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
    public record TestInstance(String name, String key, String script, String exception,
            String[] goals, Integer selectedGoal) {
    }


    public static List<Arguments> data() throws IOException, URISyntaxException {
        URL url = TestProofScriptCommand.class.getResource("cases.yml");
        if (url == null) {
            throw new FileNotFoundException("Cannot find resource 'cases'.");
        }

        var objectMapper = new ObjectMapper(new YAMLFactory());
        objectMapper.findAndRegisterModules();
        TestInstance[] instances = objectMapper.readValue(url, TestInstance[].class);
        return Arrays.stream(instances).map(Arguments::of).toList();
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
            assertTrue(props.containsKey("exception"),
                "An exception was not expected, but got " + ex.getMessage());
            // weigl: fix spurious error on Windows machine due to different file endings.
            String msg = ex.getMessage().trim().replaceAll("\r\n", "\n");
            Assertions.assertTrue(msg.startsWith(props.get("exception").trim()),
                "Unexpected exception: " + ex.getMessage() + "\n expected: "
                    + props.get("exception").trim());
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
