/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.StatisticsFile;

import org.junit.jupiter.api.*;

/**
 * This test case captures all information flow run-all-proof scenarios.
 *
 * @author M. Ulbrich
 */
@Tag("slow")
@Tag("owntest")
@Tag("testRunAllProofs")
public final class RunAllProofsInfFlow {
    @TestFactory
    Stream<DynamicTest> data() throws IOException {
        var proofCollection = InfFlowProofCollection.automaticInfFlow();
        StatisticsFile statisticsFile = proofCollection.getSettings().getStatisticsFile();
        statisticsFile.setUp();
        Assumptions.assumeTrue(proofCollection != null);
        return RunAllProofsTest.data(proofCollection);
    }

    public static void main(String[] args) throws IOException {
        GenerateUnitTests.run(Paths.get("build/generated-src/"), List.of(InfFlowProofCollection.automaticInfFlow()));
    }
}
