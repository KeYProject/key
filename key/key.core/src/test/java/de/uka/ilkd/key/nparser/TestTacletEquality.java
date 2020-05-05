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
import org.jetbrains.annotations.NotNull;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.*;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.regex.Pattern;

/**
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
        }
    }


    @Test
    public void testEquality() {
        Taclet t = findTaclet(name);
        Assume.assumeNotNull(t);
        assertEquals(expected, t.toString());
    }


    private void assertEquals(String expected, String actual) {
        Pattern normalizeWs = Pattern.compile("\\s+", Pattern.MULTILINE);
        Assert.assertEquals(
                normalise(expected).trim(),
                normalise(actual).trim()
        );
    }

    @NotNull
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
