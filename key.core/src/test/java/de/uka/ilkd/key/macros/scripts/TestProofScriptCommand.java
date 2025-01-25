/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.newsmt2.MasterHandlerTest;
import de.uka.ilkd.key.util.LineProperties;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.assertj.core.api.Assumptions.assumeThat;


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

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(tmpKey.toFile());

        Proof proof = env.getLoadedProof();

        var script = ParsingFacade.parseScript(data.script());
        ProofScriptEngine pse = new ProofScriptEngine(script);

        boolean hasException = data.exception() != null;
        try {
            pse.execute(env.getUi(), proof);
        } catch (Exception ex) {
            ex.printStackTrace();
            assertTrue(hasException,
                    "An exception was not expected, but got " + ex.getClass());
            assertThat(ex.getMessage().trim().replace("\r\n","\n"))
                    .startsWithIgnoringCase(data.exception().trim());
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
