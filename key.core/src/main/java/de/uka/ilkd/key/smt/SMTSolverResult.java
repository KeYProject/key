/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

/**
 * Encapsulates the result of a single solver.
 */
public class SMTSolverResult {

    /**
     * In the context of proving nodes/sequents these values mean the following: TRUE iff negation
     * of the sequent is unsatisfiable, FALSIFIABLE iff negation of the sequent is satisfiable (i.e.
     * it has a counterexample), UNKNOWN otherwise (I'm not sure if this holds if an error occurs)
     * Note: Currently (1.12.'09) the SMT Solvers do not check if a node is FALSE.
     */
    public enum ThreeValuedTruth {
        VALID {
            @Override
            public String toString() {
                return "valid";
            }
        },
        FALSIFIABLE {
            public String toString() {
                return "there is a counter example";
            }
        },
        UNKNOWN {
            public String toString() {
                return "unknown";
            }
        }
    }

    // We should get rid of this constant because it does not track the source (the solver) of the
    // result.
    public static final SMTSolverResult NO_IDEA =
        new SMTSolverResult(ThreeValuedTruth.UNKNOWN, "?");



    private final ThreeValuedTruth isValid;
    private static int idCounter = 0;
    private final int id = ++idCounter;

    /** This is to identify where the result comes from. E.g. for user feedback. */
    public final String solverName;

    private SMTSolverResult(ThreeValuedTruth isValid, String solverName) {
        this.solverName = solverName;

        this.isValid = isValid;
    }

    public int getID() {
        return id;
    }


    public static SMTSolverResult createValidResult(String name) {
        return new SMTSolverResult(ThreeValuedTruth.VALID, name);
    }


    public static SMTSolverResult createInvalidResult(String name) {
        return new SMTSolverResult(ThreeValuedTruth.FALSIFIABLE, name);
    }


    public static SMTSolverResult createUnknownResult(String name) {
        return new SMTSolverResult(ThreeValuedTruth.UNKNOWN, name);
    }



    public ThreeValuedTruth isValid() {
        return isValid;
    }


    public String toString() {
        return isValid.toString();
    }


    public boolean equals(Object o) {
        if (!(o instanceof SMTSolverResult)) {
            return false;
        }
        SMTSolverResult ssr = (SMTSolverResult) o;
        return isValid == ssr.isValid;
    }



}
