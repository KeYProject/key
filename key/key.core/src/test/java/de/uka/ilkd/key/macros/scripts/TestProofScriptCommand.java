package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.newsmt2.MasterHandlerTest;
import de.uka.ilkd.key.util.LineProperties;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.key_project.util.collection.ImmutableList;

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

import static org.junit.Assert.*;


/**
 * see {@link MasterHandlerTest} from where I copied quite a bit.
 */
@RunWith(Parameterized.class)
public class TestProofScriptCommand {

    @Parameter(0)
    public String name;

    @Parameter(1)
    public Path path;

    @Parameters(name = "{0}")
    public static List<Object[]> data() throws IOException, URISyntaxException {

        URL url = TestProofScriptCommand.class.getResource("cases");
        if (url == null) {
            throw new FileNotFoundException("Cannot find resource 'cases'.");
        }

        if (!url.getProtocol().equals("file")) {
            throw new IOException("Resource should be a file URL not " + url);
        }

        Path directory = Paths.get(url.toURI());
        assertTrue(Files.isDirectory(directory));

        List<Object[]> result = new ArrayList<>();
        Files.list(directory).forEach(f -> {
            Object[] item = { f.getFileName().toString(), f };
            result.add(item);
        });

        return result;
    }

    @Test
    public void testProofScript() throws Exception {

        BufferedReader reader = Files.newBufferedReader(path);
        LineProperties props = new LineProperties();
        props.read(reader);

        List<String> lines = new ArrayList<>(props.getLines("KeY"));
        Path tmpKey = Files.createTempFile("proofscript_key_" + name, ".key");
        Files.write(tmpKey, lines);

        KeYEnvironment<DefaultUserInterfaceControl> env =
                KeYEnvironment.load(tmpKey.toFile());

        Proof proof = env.getLoadedProof();

        String script = props.get("script");
        ProofScriptEngine pse = new ProofScriptEngine(script, new Location(path.toUri().toURL(), 0, 0));

        try {
            pse.execute(env.getUi(), proof);
        } catch(Exception ex) {
            assertTrue("unexpected exception", props.containsKey("exception"));
            assertEquals(ex.getMessage(), props.get("exception").trim());
            return;
        }

        assertFalse("exception would have been expected", props.containsKey("exception"));

        ImmutableList<Goal> goals = proof.openGoals();
        if(props.containsKey("goals")) {
            int expected = Integer.parseInt(props.get("goals").trim());
            assertEquals(expected, goals.size());
        }


        int no = 1;
        while(props.containsKey("goal " + no)) {
            String expected = props.get("goal " + no).trim();
            assertEquals("goal " + no, expected, goals.head().toString().trim());
            goals = goals.tail();
            no++;
        }

        if(props.containsKey("selected")) {
            Goal goal = pse.getStateMap().getFirstOpenAutomaticGoal();
            String expected = props.get("selected").trim();
            assertEquals(expected, goal.toString().trim());
        }
    }
    
}