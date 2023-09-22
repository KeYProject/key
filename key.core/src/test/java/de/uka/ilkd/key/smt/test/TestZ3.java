/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertTrue;


public class TestZ3 extends TestSMTSolver {


    public static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";
    private static final Logger LOGGER = LoggerFactory.getLogger(TestZ3.class);

    private static boolean isInstalled = false;
    private static boolean installChecked = false;

    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3 (Legacy Translation)"))
            .findFirst().orElse(null);

    @Override
    public boolean toolNotInstalled() {
        if (!installChecked) {
            isInstalled = getSolverType().isInstalled(true);
            installChecked = true;
            if (!isInstalled) {
                LOGGER.warn("Warning: {} is not installed, tests skipped.",
                    getSolverType().getName());
                LOGGER.warn(
                    "Maybe use JVM system property \"{}\" to define the path to the Z3 command.",
                    SYSTEM_PROPERTY_SOLVER_PATH);
            }

            if (isInstalled && !getSolverType().supportHasBeenChecked()) {
                if (!getSolverType().checkForSupport()) {
                    LOGGER.warn("Warning: " + "The version of the solver {} used for the "
                        + "following tests may not be supported.", getSolverType().getName());
                }
            }
        }



        return !isInstalled;
    }

    @Override
    public SolverType getSolverType() {
        SolverType type = Z3_SOLVER;
        String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
        if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
            type.setSolverCommand(solverPathProperty);
        }
        return type;
    }

    // These testcases are z3 specific, because other solvers don't support integer division.
    @Test
    public void testDiv1() throws Exception {
        assertTrue(correctResult(testFile + "div1.key", true));
    }

    @Test
    public void testDiv3() throws Exception {
        assertTrue(correctResult(testFile + "div3.key", true));
    }

    @Test
    public void testDiv5() throws Exception {
        assertTrue(correctResult(testFile + "div5.key", false));
    }

    @Test
    public void testDiv6() throws Exception {
        assertTrue(correctResult(testFile + "div6.key", false));
    }

}
