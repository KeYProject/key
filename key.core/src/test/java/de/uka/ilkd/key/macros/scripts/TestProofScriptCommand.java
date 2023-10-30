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
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.newsmt2.MasterHandlerTest;
import de.uka.ilkd.key.util.LineProperties;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import static org.junit.jupiter.api.Assertions.assertTrue;


/**
 * see {@link MasterHandlerTest} from where I copied quite a bit.
 */
public class TestProofScriptCommand {
    public static List<Arguments> data() throws IOException, URISyntaxException {
        URL url = TestProofScriptCommand.class.getResource("cases");
        if (url == null) {
            throw new FileNotFoundException("Cannot find resource 'cases'.");
        }

        if (!url.getProtocol().equals("file")) {
            throw new IOException("Resource should be a file URL not " + url);
        }

        Path directory = Paths.get(url.toURI());
        assertTrue(Files.isDirectory(directory));
        try (var s = Files.list(directory)) {
            return s.map(f -> Arguments.of(f.getFileName().toString(), f))
                    .collect(Collectors.toList());
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    void testProofScript(String name, Path path) throws Exception {

        BufferedReader reader = Files.newBufferedReader(path);
        LineProperties props = new LineProperties();
        props.read(reader);

        List<String> lines = new ArrayList<>(props.getLines("KeY"));
        Path tmpKey = Files.createTempFile("proofscript_key_" + name, ".key");
        Files.write(tmpKey, lines);

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(tmpKey.toFile());

        Proof proof = env.getLoadedProof();

        String script = props.get("script");
        ProofScriptEngine pse =
            new ProofScriptEngine(script,
                new Location(path.toUri(), Position.newOneBased(1, 1)));

        try {
            pse.execute(env.getUi(), proof);
        } catch (Exception ex) {
            assertTrue(props.containsKey("exception"), "unexpected exception");
            Assertions.assertEquals(ex.getMessage(), props.get("exception").trim());
            return;
        }

        Assertions.assertFalse(props.containsKey("exception"),
            "exception would have been expected");

        ImmutableList<Goal> goals = proof.openGoals();
        if (props.containsKey("goals")) {
            int expected = Integer.parseInt(props.get("goals").trim());
            Assertions.assertEquals(expected, goals.size());
        }


        int no = 1;
        while (props.containsKey("goal " + no)) {
            String expected = props.get("goal " + no).trim();
            Assertions.assertEquals(expected, goals.head().toString().trim(), "goal " + no);
            goals = goals.tail();
            no++;
        }

        if (props.containsKey("selected")) {
            Goal goal = pse.getStateMap().getFirstOpenAutomaticGoal();
            String expected = props.get("selected").trim();
            Assertions.assertEquals(expected, goal.toString().trim());
        }
    }

}
