/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.test;


import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TestCvc4 extends TestSMTSolver {
    private static final String SYSTEM_PROPERTY_SOLVER_PATH = "cvc4SolverPath";
    private static final Logger LOGGER = LoggerFactory.getLogger(TestCvc4.class);

    private static boolean isInstalled = false;
    private static boolean installChecked = false;

    public static final SolverType CVC4_SOLVER =
        SolverTypes.getSolverTypes().stream()
                .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                        && it.getName().equals("CVC4 (Legacy Translation)"))
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
                    "Maybe use JVM system property \"{}\" to define the path to the CVC4 command.",
                    SYSTEM_PROPERTY_SOLVER_PATH);
            }
            if (isInstalled && !getSolverType().supportHasBeenChecked()) {
                if (!getSolverType().checkForSupport()) {
                    LOGGER.warn(
                        "Warning: The version of the solver {}"
                            + " used for the following tests may not be supported.",
                        getSolverType().getName());
                }
            }
        }
        return !isInstalled;
    }

    @Override
    public SolverType getSolverType() {
        SolverType type = CVC4_SOLVER;
        String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
        if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
            type.setSolverCommand(solverPathProperty);
        }
        return type;
    }
}
