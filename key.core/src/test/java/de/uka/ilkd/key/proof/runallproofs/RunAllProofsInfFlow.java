package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.StatisticsFile;

import org.junit.jupiter.api.*;

/**
 * This test case captures all information flow run-all-proof scenarios.
 * <p>
 * The test case is controlled by the index file (see {@value #INDEX_FILE}).
 * <p>
 * If the property "{@value #SKIP_INF_FLOW_PROPERTY}" is set to true, then no info-flow
 * run-all-proof tests will be run.
 *
 * @author M. Ulbrich
 */
@Tag("slow")
@Tag("owntest")
@Tag("testRunAllProofs")
public final class RunAllProofsInfFlow extends RunAllProofsTest {
    private static final String SKIP_INF_FLOW_PROPERTY = "key.runallproofs.skipInfFlow";
    public static final String INDEX_FILE = "index/automaticInfFlow.txt";
    private static final ProofCollection proofCollection = getProofCollection();

    private static ProofCollection getProofCollection() {
        if (!Boolean.getBoolean(SKIP_INF_FLOW_PROPERTY)) {
            try {
                return parseIndexFile(INDEX_FILE);
            } catch (IOException e) {
                Assertions.fail(e);
            }
        }
        return null;
    }

    @TestFactory
    Stream<DynamicTest> data() throws IOException {
        Assumptions.assumeTrue(proofCollection != null);
        return data(proofCollection);
    }

    @BeforeAll
    public static void setUpStatisticsFile() throws IOException {
        StatisticsFile statisticsFile = proofCollection.getSettings().getStatisticsFile();
        statisticsFile.setUp();
    }

    @AfterAll
    public static void computeSumsAndAverages() throws IOException {
        StatisticsFile statisticsFile = proofCollection.getSettings().getStatisticsFile();
        statisticsFile.computeSumsAndAverages();
    }
}
