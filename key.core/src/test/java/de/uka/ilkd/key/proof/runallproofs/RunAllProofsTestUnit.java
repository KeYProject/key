/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A single unit that will be tested during {@link RunAllProofsTest} run.
 *
 * @author Kai Wallisch
 */
public final class RunAllProofsTestUnit implements Serializable {
    private static final long serialVersionUID = -2406881153415390252L;
    private static final Logger LOGGER = LoggerFactory.getLogger(StatisticsFile.class);

    /**
     * The name of this test.
     */
    private final String testName;

    private final ProofCollectionSettings settings;
    private final List<TestFile> testFiles;
    private final boolean ungrouped;

    /**
     * Method {@link Object#toString()} is used by class {@link RunAllProofsTest} to determine the
     * name of a test case. It is overridden here so that test cases can be easily recognized by
     * their name.
     */
    @Override
    public String toString() {
        return testName;
    }

    public RunAllProofsTestUnit(String name, ProofCollectionSettings settings,
            List<TestFile> testFiles, boolean ungrouped) {
        this.testName = name;
        this.settings = settings;
        this.testFiles = testFiles;
        this.ungrouped = ungrouped;
    }

    /**
     * Run the test of this unit and return a {@link TestResult}.
     *
     * If {@link #ungrouped} is true, the result is the result of that single test. Otherwise all
     * results are aggregated into a single testresult.
     *
     * The way of execution is determined by the {@link #settings}, in particular by the
     * {@link ProofCollectionSettings#getForkMode() forkmode}.
     *
     * @return either a single test result or an aggregated test result, not <code>null</code>.
     * @param xml
     */
    public TestResult runTest(JunitXmlWriter xml) throws Exception {
        /*
         * List of test results containing one test result for each test file contained in this
         * group.
         */
        List<TestResult> testResults;

        boolean verbose = settings.getVerboseOutput();
        if (verbose) {
            LOGGER.info("Running test " + testName);
        }

        boolean ignoreTest = settings.getIgnoreTest();
        if (ignoreTest) {
            if (verbose) {
                LOGGER.info("... ignoring this test due to 'ignore=true' in file");
            }
            return new TestResult("Test case has been ignored", true);
        }

        ForkMode forkMode = settings.getForkMode();
        switch (forkMode) {
        case PERGROUP:
            testResults = ForkedTestFileRunner.processTestFiles(testFiles, getTempDir());
            break;

        case NOFORK:
            testResults = new ArrayList<>();
            for (TestFile testFile : testFiles) {
                TestResult testResult = testFile.runKey();
                testResults.add(testResult);
            }
            break;

        case PERFILE:
            testResults = new ArrayList<>();
            for (TestFile testFile : testFiles) {
                TestResult testResult =
                    ForkedTestFileRunner.processTestFile(testFile, getTempDir());
                testResults.add(testResult);
            }
            break;

        default:
            throw new RuntimeException("Unexpected value for fork mode: " + forkMode);
        }

        if (verbose) {
            LOGGER.info("Returning from test " + testName);
        }

        /*
         * Merge list of test results into one single test result, unless it is a singleton case
         * outside any group declaration.
         */
        if (ungrouped) {
            assert testResults.size() == 1 : "Ungrouped test runs must have one case";
            return testResults.get(0);
        }

        boolean success = true;
        StringBuilder message = new StringBuilder("group " + testName + ":\n");
        for (int i = 0; i < testResults.size(); i++) {
            var start = System.currentTimeMillis();
            TestFile file = testFiles.get(i);
            var time = System.currentTimeMillis() - start;
            TestResult testResult = testResults.get(i);
            xml.addTestcase(file.getKeYFile().getName(), this.testName,
                (testResult.success ? JunitXmlWriter.TestCaseState.SUCCESS
                        : JunitXmlWriter.TestCaseState.FAILED),
                "",
                !testResult.success ? "error" : "", testResult.message, "", time / 1000.0);
            success &= testResult.success;
            message.append(testResult.message).append("\n");
        }
        return new TestResult(message.toString(), success);
    }

    public String getTestName() {
        return testName;
    }

    /*
     * Temporary directory used by this test unit to store serialized data when running in fork
     * mode.
     */
    private Path tempDir = null;

    public Path getTempDir() throws IOException {
        File runAllProofsTempDir = settings.getTempDir();
        if (tempDir == null) {
            if (!runAllProofsTempDir.exists()) {
                runAllProofsTempDir.mkdirs();
            }
            tempDir = Files.createTempDirectory(runAllProofsTempDir.toPath(), testName + "-");
        }
        return tempDir;
    }

    public List<TestFile> getTestFiles() {
        return testFiles;
    }

    public ProofCollectionSettings getSettings() {
        return settings;
    }

    public int getTotalNumTests() {
        return this.testFiles.size();
    }
}
