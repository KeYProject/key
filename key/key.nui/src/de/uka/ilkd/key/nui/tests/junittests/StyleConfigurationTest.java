package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.stream.Stream;

import org.junit.BeforeClass;
import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyler;
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
     * The proof file used for this test.
     */
    private static String TESTFILE_01 = "resources//de/uka//ilkd//key//examples//example01.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private static ProofTreeConverter ptVisualizer;

    @BeforeClass
    public static void setUpBeforeClass() {
        File proofFileName = new File(TESTFILE_01);
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
    }

    @Test
    public void StyleConfigurationTest01() {
        ProofTreeStyler ptStyler = new ProofTreeStyler(null);
        Stream<NUINode> nstream = ptVisualizer.getRootNode().asList().stream()
                .filter((nd) -> (!(nd.getStyleConfiguration()
                        .equals(ptStyler.getStyleConfiguration(nd)))));
        assertEquals(nstream.count(), 0);
    }
}
