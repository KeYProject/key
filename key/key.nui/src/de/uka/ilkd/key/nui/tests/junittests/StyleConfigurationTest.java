package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.assertTrue;

import java.io.File;

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
 * @author Patrick Jattke
 *
 */
public class StyleConfigurationTest {

    /**
     * The absolute path to the directory containing the test files.
     */
    //private static String TESTFILES_DIRECTORY = "../../../examples/";
    private static String TESTFILES_DIRECTORY  = "resources//de//uka//ilkd//key//examples//";
    /**
     * The proof file used for this test.
     */
    private static String TESTFILE_01 = "example01.proof";
    private static String TESTFILE_02 = "example02.proof";
    private static String TESTFILE_03 = "gcd.twoJoins.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private ProofTreeConverter ptVisualizer;

    public NUINode loadVisualizer(String testfileName) {
        File proofFileName = new File(TESTFILES_DIRECTORY + testfileName);
        // load proof
        KeYEnvironment<?> environment = null;
        try {
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                    proofFileName, null, null, null, true);
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
        }
        final Proof proof = environment.getLoadedProof();
        proof.setProofFile(proofFileName);

        // initalize ProofConverter object used for tests
        ptVisualizer = new ProofTreeConverter(proof);

        // return root node of the created tree
        return ptVisualizer.getRootNode();
    }

    @Test
    public void StyleConfigurationTest01() {
        NUINode node = loadVisualizer(TESTFILE_01);
        checkTree(node);
    }

    @Test
    public void StyleConfigurationTest02() {
        NUINode node = loadVisualizer(TESTFILE_02);
        checkTree(node);
    }

    @Test
    public void StyleConfigurationTest03() {
        NUINode node = loadVisualizer(TESTFILE_03);
        checkTree(node);
    }

    /**
     * Checks for the whole subtree, rooted by the given {@link NUINode} node,
     * if every node has the right {@link StyleConfiguration} assigned to.
     * 
     * @param node
     */
    private void checkTree(NUINode node) {
        for (NUINode n : node.asList()) {
            checkStyleConfiguration(n);
        }
    }

    /**
     * Checks whether the given {@link NUINode} node has the right
     * {@link StyleConfiguration} assigned to.
     * 
     * @param node
     */
    private void checkStyleConfiguration(NUINode node) {
        ProofTreeStyler ptStyler = new ProofTreeStyler(null);
        StyleConfiguration nodeConfig = node.getStyleConfiguration();
        StyleConfiguration desiredConfig = ptStyler.getStyleConfiguration(node);
        assertTrue("StyleConfiguration of node is not correct!",
                nodeConfig.equals(desiredConfig));
    }

}
