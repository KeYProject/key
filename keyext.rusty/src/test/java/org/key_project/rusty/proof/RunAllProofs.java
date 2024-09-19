/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.io.IOException;
import java.util.stream.Stream;

import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.TestFactory;

@Tag("testRunAllProofs")
public final class RunAllProofs {
    @TestFactory
    Stream<DynamicTest> data() throws IOException {
        var proofCollection = ProofCollections.automaticRustyDL();
        var statsFile = proofCollection.getSettings().getStatisticsFile();
        statsFile.setUp();
        return RunAllProofsTest.data(proofCollection);
    }
}
