/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

/**
 * Encapsulates the result of a single solver.
 */
public class SMTSolverResult {

    /**
     * This enum represents the three possible outcomes of an external SMT solver call.
     */
    public enum ThreeValuedTruth {
        /**
         * The sequent is valid, i.e. the negation of the sequent is unsatisfiable.
         */
        VALID {
            @Override
            public String toString() {
                return "valid";
            }
        },
        /**
         * The sequent is falsifiable, i.e. the negation of the sequent is satisfiable (it has a
         * counterexample).
         */
        FALSIFIABLE {
            public String toString() {
                return "there is a counter example";
            }
        },
        /**
         * The solver could not determine the validity of the sequent.
         */
        UNKNOWN {
            public String toString() {
                return "unknown";
            }
        }
    }

    // We should get rid of this constant because it does not track the source (the solver) of the
    // result.
    public static final SMTSolverResult NO_IDEA =
        new SMTSolverResult(ThreeValuedTruth.UNKNOWN, "?", false);

    private final ThreeValuedTruth isValid;
    private static int idCounter = 0;
    private final int id = ++idCounter;

    /** This is to identify where the result comes from. E.g. for user feedback. */
    private final String solverName;

    /**
     * Indicates that the solver timed out. Should only be used in combination with unknown result.
     */
    private final boolean timeout;

    private SMTSolverResult(ThreeValuedTruth isValid, String solverName, boolean timeout) {
        this.solverName = solverName;
        this.isValid = isValid;
        this.timeout = timeout;
    }

    public int getID() {
        return id;
    }


    public static SMTSolverResult createValidResult(String name) {
        return new SMTSolverResult(ThreeValuedTruth.VALID, name, false);
    }


    public static SMTSolverResult createInvalidResult(String name) {
        return new SMTSolverResult(ThreeValuedTruth.FALSIFIABLE, name, false);
    }


    public static SMTSolverResult createUnknownResult(String name, boolean timeout) {
        return new SMTSolverResult(ThreeValuedTruth.UNKNOWN, name, timeout);
    }

    public ThreeValuedTruth isValid() {
        return isValid;
    }


    public String toString() {
        return isValid.toString();
    }


    public boolean equals(Object o) {
        if (!(o instanceof SMTSolverResult ssr)) {
            return false;
        }
        return isValid == ssr.isValid;
    }



}
