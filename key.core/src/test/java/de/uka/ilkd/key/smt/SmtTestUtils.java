/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;

/**
 * @author Alexander Weigl
 * @version 1 (5/5/25)
 */
public class SmtTestUtils {

    /// Variable signals whether a missing SMT solver should result into a abortion of the test
    /// cases or a failing of the test case.
    /// Flag is triggered by the environment variable `failIfSmtSolverIsUnavailable` or
    /// `GITHUB_ACTIONS`.
    public static final boolean failIfSmtSolverIsUnavailable =
        Boolean.parseBoolean(System.getenv("failIfSmtSolverIsUnavailable"))
                || Boolean.parseBoolean(System.getenv("GITHUB_ACTIONS"));

    private static final String REQUIRED_SMT_SOLVER_NOT_INSTALLED =
        "required SMT solver not installed";


    /// Return true if z3 is installed. This means an {@link
    /// de.uka.ilkd.key.smt.solvertypes.SolverType}
    /// for z3 is available and it returned true for being installed.
    ///
    /// @see de.uka.ilkd.key.smt.solvertypes.SolverType#isInstalled(boolean)
    public static boolean z3Installed() {
        return SolverTypes.getSolverTypes().stream()
                .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                        && it.getName().equals("Z3"))
                .findFirst().map(x -> x.isInstalled(true)).orElse(false);
    }

    /// Assumes or assert that z3 is installed depending on [#failIfSmtSolverIsUnavailable]
    public static void assumeZ3Installed() {
        var isInstalled = z3Installed();
        assumeSmtIsInstalled(isInstalled);
    }

    /// Assumes or assert that the SMT is not installed depending on [#failIfSmtSolverIsUnavailable]
    public static void assumeSmtIsInstalled(boolean isInstalled) {
        if (!isInstalled && !failIfSmtSolverIsUnavailable) {
            Assumptions.abort(REQUIRED_SMT_SOLVER_NOT_INSTALLED);
        }

        if (!isInstalled && failIfSmtSolverIsUnavailable) {
            Assertions.fail(REQUIRED_SMT_SOLVER_NOT_INSTALLED);
        }
    }
}
