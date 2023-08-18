/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Tag;

/**
 * <p>
 * This class uses the provided example files from KeY for test purpose on the same way as the
 * bin/runAllProofs.pl does it.
 * </p>
 *
 * <p>
 * RunAllProofs documentation can be found at the following location in KeY git repository:
 * key/doc/README.runAllProofs
 * </p>
 *
 * <p>
 * The files to test are listed in: <br />
 * $KEY_HOME/key.core/src/test/resources/testcase/runallproofs/automaticJAVADL.txt
 * </p>
 *
 * <p>
 * The test steps for each defined test file are:
 * <ol>
 * <li>Create a copy with extension ".auto.key". The file contains the default settings from
 * examples/index/headerJavaDL.txt if required.</li>
 * <li>A new Java process is started for each test file. It executes Main#main with the file as
 * parameter and additional parameter {@code auto}.</li>
 * <li>The process termination result must be {@code 0} if the proof is closed and something
 * different otherwise. This value is used to determine the test result.</li>
 * </ol>
 * </p>
 * <p>
 * This class can be executed as "JUnit plug-in test" without extra configurations. For execution as
 * normal "Junit test" it is required to define the system properties "key.home" and "key.lib" like:
 * {@code "-Dkey.home=D:/Forschung/GIT/KeY" "-Dkey.lib=D:/Forschung/Tools/KeY-External Libs"} .
 * </p>
 * <p>
 * This class itself does not define testcases. The class has subclasses which define test cases for
 * different run-all-proof scenarios.
 *
 * @author Martin Hentschel
 */
@Tag("slow")
public final class RunAllProofsTest {

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
            Assertions.assertTrue(report.success, report.message);
        }
    }
}
