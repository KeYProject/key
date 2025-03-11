/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.StatisticsFile;

import org.junit.jupiter.api.*;

/**
 * This test case captures all information flow run-all-proof scenarios.
 * <p>
 * The test case is controlled by the index file (see {@value #INDEX_FILE}).
 * <p>
 * If the property "{@value #SKIP_INF_FLOW_PROPERTY}" is set to true, then no
 * info-flow
 * run-all-proof tests will be run.
 *
 * @author M. Ulbrich
 */
@Tag("slow")
@Tag("owntest")
@Tag("testRunAllProofs")
public final class RunAllProofsInfFlow {
    @TestFactory
    Stream<DynamicTest> data() throws IOException {
        var proofCollection = ProofCollections.automaticInfFlow();
        StatisticsFile statisticsFile = proofCollection.getSettings().getStatisticsFile();
        statisticsFile.setUp();
        Assumptions.assumeTrue(proofCollection != null);
        return RunAllProofsTest.data(proofCollection);
    }
}
