/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.stream.Stream;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;

public class RunAllProofsTest {
    /**
     * Creates a set of constructor parameters for this class. Uses JUnits parameterized test case
     * mechanism for to create several test cases from a set of data. {@link Object#toString()} of
     * first constructor parameter is used to determine name of individual test cases, see
     * {@link RunAllProofsTestUnit#toString()} for further information.
     *
     * @param proofCollection The file name of the index file which parsed to produce test cases
     * @return The parameters. Each row will be one test case.
     * @throws IOException If an exceptions occurs while reading and parsing the index file
     */
    public static Stream<DynamicTest> data(ProofCollection proofCollection) throws IOException {
        /*
         * Create list of constructor parameters that will be returned by this method. Suitable
         * constructor is automatically determined by JUnit.
         */
        List<RunAllProofsTestUnit> units = proofCollection.createRunAllProofsTestUnits();
        new File("build/test-results/rap/").mkdirs();
        return units.stream()
                .map(unit -> DynamicTest.dynamicTest(unit.getTestName(), () -> executeUnit(unit)));
    }

    private static void executeUnit(RunAllProofsTestUnit unit) throws Exception {
        /*
         * Tests each file defined by the instance variables. The tests steps are described in
         * the
         * constructor of this class.
         */
        String xmlFile = String.format("build/test-results/rap/%s.xml", unit.getTestName());
        try (JunitXmlWriter xml =
            new JunitXmlWriter(new FileWriter(xmlFile), "runallproofs." + unit.getTestName())) {
            TestResult report = unit.runTest(xml);
            Assertions.assertTrue(report.success(), report.message());
        }
    }
}
