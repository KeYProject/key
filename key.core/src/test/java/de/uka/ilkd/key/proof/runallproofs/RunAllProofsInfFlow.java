package de.uka.ilkd.key.proof.runallproofs;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.StatisticsFile;
import org.antlr.runtime.RecognitionException;
import org.junit.jupiter.api.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import java.io.File;

import java.io.IOException;
import java.util.stream.Stream;

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
    private static final Logger LOGGER = LoggerFactory.getLogger(RunAllProofsInfFlow.class);
    private static final String SKIP_INF_FLOW_PROPERTY = "key.runallproofs.skipInfFlow";
    public static final String INDEX_FILE = "index/automaticInfFlow.txt";
    private static ProofCollection proofCollection = getProofCollection();

    static {
        LOGGER.info("The property {} is {}", SKIP_INF_FLOW_PROPERTY,
            Boolean.getBoolean(SKIP_INF_FLOW_PROPERTY));
        LOGGER.info("Using index file {}", new File(INDEX_FILE));
    }

    private static ProofCollection getProofCollection() {
        if (!Boolean.getBoolean(SKIP_INF_FLOW_PROPERTY)) {
            try {
                return parseIndexFile(INDEX_FILE);
            } catch (IOException e) {
                LOGGER.error("Could not read {}", INDEX_FILE, e);
                Assertions.fail();
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
