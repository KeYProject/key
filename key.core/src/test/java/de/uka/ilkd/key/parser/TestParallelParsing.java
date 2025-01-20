/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.parser.schemajava.SchemaJavaParser;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Test;

/**
 * This TestCase tests the parallel usage of {@link de.uka.ilkd.key.nparser.KeYParser} and
 * {@link SchemaJavaParser}.
 *
 * @author Martin Hentschel
 */
public class TestParallelParsing {
    /**
     * Loads both proof files contained in {@code "examples/_testcase/parser/MultipleRecursion"} in
     * parallel using {@code 4} {@link Thread}s in total.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testLoadingOfTwoDifferentProofFiles() throws Exception {
        doParallelTest(HelperClassForTests.TESTCASE_DIRECTORY, 2,
            "parser/MultipleRecursion/MultipleRecursion[MultipleRecursion__a()]_JML_normal_behavior_operation_contract_0.proof",
            "parser/MultipleRecursion/MultipleRecursion[MultipleRecursion__b()]_JML_normal_behavior_operation_contract_0.proof");
    }

    /**
     * Executes the test steps.
     *
     * @param baseDir The base directory.
     * @param numOfThreadsPerLocation The number of {@link Thread}s per location.
     * @param locations The locations to load.
     * @throws Exception Occurred Exception.
     */
    protected void doParallelTest(File baseDir, int numOfThreadsPerLocation, String... locations)
            throws Exception {
        boolean originalOneStepSimplification =
            HelperClassForTests.isOneStepSimplificationEnabled(null);
        try {
            HelperClassForTests.setOneStepSimplificationEnabled(null, true);
            // Create threads
            List<LoadThread> threads = new LinkedList<>();
            for (String path : locations) {
                for (int i = 0; i < numOfThreadsPerLocation; i++) {
                    final File location = new File(baseDir, path);
                    threads.add(new LoadThread(location));
                }
            }
            // Start threads
            for (LoadThread thread : threads) {
                thread.start();
            }
            // Wait for threads
            for (LoadThread thread : threads) {
                try {
                    thread.join();
                } catch (InterruptedException ignored) {
                }
            }
            // Test results
            for (LoadThread thread : threads) {
                if (thread.getException() != null) {
                    throw thread.getException();
                }
            }
        } finally {
            // Restore original options
            HelperClassForTests.setOneStepSimplificationEnabled(null,
                originalOneStepSimplification);
        }
    }

    /**
     * Helper {@link Thread} used by
     * {@link TestParallelParsing#doParallelTest(File, int, String...)} to load a location in KeY.
     *
     * @author Martin Hentschel
     */
    private static class LoadThread extends Thread {
        /**
         * The location to load.
         */
        private final File location;

        /**
         * Occurred {@link Exception}.
         */
        private Exception exception;

        /**
         * Constructor.
         *
         * @param location The location to load.
         */
        public LoadThread(File location) {
            this.location = location;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public void run() {
            try {
                KeYEnvironment<DefaultUserInterfaceControl> env =
                    KeYEnvironment.load(new JavaProfile(), location, null, null, null, false);
                env.dispose();
            } catch (Exception e) {
                exception = e;
            }
        }

        /**
         * Returns the occurred {@link Exception}.
         *
         * @return The occurred {@link Exception}.
         */
        public Exception getException() {
            return exception;
        }
    }
}
