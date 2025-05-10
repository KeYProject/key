/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.test;

import java.io.File;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.*;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.slf4j.Logger;

/**
 * Concrete instances of this class test that some .key files are translated to SMT-LIB correctly
 * and the SMT solver has a specified behavior on them (returns unsat, sat, or unknown/timeout).
 * <p>
 * Note: The settings for the solver are hard-coded in {@link de.uka.ilkd.key.smt.SMTTestSettings}!
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public abstract class SMTSolverTest extends SMTTestCommons {
    public static final String TEST_DIR =
        HelperClassForTests.TESTCASE_DIRECTORY + File.separator + "smt" + File.separator;

    protected boolean isInstalled = false;
    protected boolean installChecked = false;

    protected abstract Logger getLogger();

    protected abstract String getSystemPropertySolverPath();

    protected abstract String getSolverName();

    @Override
    public boolean toolInstalled() {
        if (!installChecked) {
            SolverType solverType = getSolverType();
            isInstalled = solverType != null && solverType.isInstalled(true);
            installChecked = true;
            if (!isInstalled) {
                getLogger().warn("Warning: {} is not installed, tests skipped.",
                    getSolverName());
                getLogger().warn(
                    "Maybe use JVM system property \"{}\" to define the path to the solver binary.",
                    getSystemPropertySolverPath());
            } else if (!solverType.supportHasBeenChecked()) {
                if (!solverType.checkForSupport()) {
                    getLogger().warn("Warning: The version of the solver {}"
                        + " used for the following tests may not be supported.",
                        getSolverName());
                }
            }
        }
        return isInstalled;
    }

    /**
     * Provides arguments for the parameterized test
     * {@link #test(SMTSolverResult.ThreeValuedTruth, String)}.
     *
     * @return the stream of arguments
     */
    protected abstract Stream<Arguments> provideTestData();

    @MethodSource("provideTestData")
    @ParameterizedTest(name = "test {1}")
    public void test(SMTSolverResult.ThreeValuedTruth expected, String filename)
            throws ProblemLoaderException {
        SMTSolverResult.ThreeValuedTruth actual = getResult(expected, TEST_DIR + filename);
        Assertions.assertSame(expected, actual, "Expected \"" + expected.name() + "\" for "
            + filename + ", but result was \"" + actual.name() + "\"!");
    }
}
