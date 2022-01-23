package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import javax.annotation.Nonnull;
import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;

/**
 * This class provides regression tests for KeY Taclets.
 *
 * <p>
 * This class uses a default project to boostrap a {@link de.uka.ilkd.key.control.KeYEnvironment} and print all
 * registered taclets. For the string representation of taclets, the {@link Taclet#toString()} method is used.
 * So do not expect anything fancy. Later, the actual printout of each taclet is compared to the latest version defined
 * in {@code taclets.old.txt}.
 * </p>
 *
 * <h2>How to update {@code taclet.old.txt} efficiently.</h2>
 * <p>
 * You can generate a new oracle easily by invoking the disabled test-method {@link #createNewOracle()}.
 * This method generates the {@code taclet.new.txt} file. Then, you should use a diff-tool to compare the changes
 * or directly overwrite {@code taclets.old.txt} with the new representations.
 *
 * @author Alexander Weigl
 * @version 1 (5/5/20)
 */
@RunWith(Parameterized.class)
public class TestTacletEquality {

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> createCases() throws IOException {
        InputStream is = TestTacletEquality.class.getResourceAsStream("taclets.old.txt");
        Assume.assumeNotNull(is);
        LinkedList<Object[]> seq = new LinkedList<>();
        try (BufferedReader r = new BufferedReader(new InputStreamReader(is))) {
            String tmp;
            while ((tmp = r.readLine()) != null) {
                if (tmp.trim().isEmpty()) continue;
                if (tmp.startsWith("#")) continue;
                if (tmp.startsWith("== ")) {
                    StringBuilder expected = new StringBuilder();
                    int nameEnd = tmp.indexOf(' ', 4);
                    String name = tmp.substring(3, nameEnd + 1).trim();
                    while ((tmp = r.readLine()) != null) {
                        if (tmp.trim().isEmpty()) continue;
                        if (tmp.startsWith("#")) continue;
                        if (tmp.startsWith("---")) {
                            seq.add(new Object[]{
                                    name, expected.toString()});
                            break;
                        }
                        expected.append(tmp).append("\n");
                    }
                }
            }
        }
        return seq;
    }

    @Parameterized.Parameter(value = 0)
    public String name;
    @Parameterized.Parameter(value = 1)
    public String expected;


    private static InitConfig initConfig;

    @Before
    public void setUp() throws ProofInputException, IOException, ProblemLoaderException {
        File file = new File(HelperClassForTests.TESTCASE_DIRECTORY, "merge/gcd.closed.proof");
        if (initConfig == null) {
            ProblemLoaderControl control = new DefaultUserInterfaceControl(null);
            SingleThreadProblemLoader loader = new SingleThreadProblemLoader(
                    file, null, null, null, JavaProfile.getDefaultInstance(),
                    true, control, false, null);
            loader.load();
            initConfig = loader.getInitConfig();
            //uncomment the line, if you want to generate a new oracle file
            //createNewOracle();
        }
    }

    public void createNewOracle() {
        var path = Paths.get("src/test/resources/de/uka/ilkd/key/nparser/taclets.new.txt");
        var taclets = new ArrayList<>(initConfig.activatedTaclets());
        //sort by name
        taclets.sort(Comparator.comparing(it -> it.name().toString()));

        try (var out = new PrintWriter(Files.newBufferedWriter(path))) {
            out.write("# This files contains representation of taclets, which are accepted and revised.\n");
            out.format("# Date: %s\n\n", new Date());
            for (Taclet taclet : taclets) {
                out.format("== %s (%s) =========================================\n",
                        taclet.name(), taclet.displayName());
                out.println(taclet);
                out.format("-----------------------------------------------------\n");
            }
        } catch (IOException e) {
            System.out.println("Exception for opening " + path);
            e.printStackTrace();
        }
    }

    @Test
    public void testEquality() {
        Taclet t = findTaclet(name);
        Assume.assumeNotNull(t);
        assertEquals(expected, t.toString());
    }


    private void assertEquals(String expected, String actual) {
        Assert.assertEquals(
                normalise(expected).trim(),
                normalise(actual).trim()
        );
    }

    @Nonnull
    private String normalise(String expected) {
        return expected.replaceAll("\\s+", "\n")
                .replaceAll("Choices:\\s*\\{.*?\\}", "");
    }

    final HashMap<String, Taclet> cache = new HashMap<>();

    private Taclet findTaclet(String name) {
        if (cache.isEmpty()) {
            for (Taclet taclet : initConfig.activatedTaclets()) {
                cache.put(taclet.name().toString(), taclet);
            }
        }
        return cache.get(name);
    }
}
