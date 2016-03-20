package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import java.io.File;
import java.util.stream.Stream;
import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyler;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyler.StyleConfiguration;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Test for User Stories
 * <ul>
 * <li>Icons im Beweisbaum #14470
 * <li>Farbige Hinterlegung von Knoten im Beweisbaum #14662
 * </ul>
 * 
 * This test go through each node of the tree and checks whether the
 * {@link StyleConfiguration} stored in the {@link NUINode} is the right one for
 * this specific node.
 * 
 * @author Patrick Jattke
 *
 */
public class StyleConfigurationTest {

    /**
     * The testfile 01 used for the tests.
     */

    private static String TESTFILE_01 = "resources//de/uka//ilkd//key//examples//example01.proof";

    /**
     * The testfile 02 used for the tests.
     */
    private static String TESTFILE_02 = "resources//de/uka//ilkd//key//examples//example02.proof";

    /**
     * The testfile 03 used for the tests.
     */
    private static String TESTFILE_03 = "resources//de/uka//ilkd//key//examples//gcd.twoJoins.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private static ProofTreeConverter ptVisualizer;

    /**
     * Prepares the test environment by using the provided path to the test
     * file.
     * 
     * @param testfilePath
     *            The path to the test file to load.
     */
    public static void prepareTest(final String testfilePath) {
        final File proofFileName = new File(testfilePath);

        // load proof
        KeYEnvironment<?> environment = null;
        try {
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFileName, null,
                    null, null, true);
        }
        catch (ProblemLoaderException e) {
            throw new RuntimeException(e);
        }

        final Proof proof = environment.getLoadedProof();

        if (proof == null) {
            fail("Proof file could not be loaded.");

        }
        else {

            proof.setProofFile(proofFileName);

            // initialize ProofConverter object used for tests
            ptVisualizer = new ProofTreeConverter(proof);
        }
    }

    /**
     * Checks whether the {@link StyleConfiguration} applied to
     * {@link #TESTFILE_01} is correct.
     */
    @Test
    public void styleConfigurationTest01() {
        prepareTest(TESTFILE_01);
        assertEquals(checkConfiguration(), 0);
    }

    /**
     * Checks whether the {@link StyleConfiguration} applied to
     * {@link #TESTFILE_02} is correct.
     */
    @Test
    public void styleConfigurationTest02() {
        prepareTest(TESTFILE_02);
        assertEquals(checkConfiguration(), 0);
    }

    /**
     * Checks whether the {@link StyleConfiguration} applied to
     * {@link #TESTFILE_03} is correct.
     */
    @Test
    public void styleConfigurationTest03() {
        prepareTest(TESTFILE_03);
        assertEquals(checkConfiguration(), 0);
    }

    /**
     * Checks whether the {@link StyleConfiguration} stored in each
     * {@link NUINode} is the correct one determined by the node's properties.
     * 
     * @return The number of nodes which have an incorrect StyleConfiguration
     *         assigned.
     */

    private static int checkConfiguration() {
        final ProofTreeStyler ptStyler = new ProofTreeStyler(null);
        final Stream<NUINode> nstream = ptVisualizer.getRootNode().asList().stream().filter(
                (nd) -> (!(nd.getStyleConfiguration().equals(ptStyler.getStyleConfiguration(nd)))));

        return ((int) nstream.count());
    }
}
