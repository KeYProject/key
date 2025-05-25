/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.smt.communication.SolverCommunication;

/**
 * Encapsulates the result of a single solver.
 */
public abstract class SMTSolverResult {

    /**
     * Solver this result belongs to
     */
    private final SMTSolver solver;
    private final SMTProblem problem;
    private final long timeTaken;
    private final SolverCommunication solverCommunication;

    /**
     * In the context of proving nodes/sequents these values mean the following: TRUE iff negation
     * of the sequent is unsatisfiable, FALSIFIABLE iff negation of the sequent is satisfiable (i.e.
     * it has a counterexample), UNKNOWN otherwise (I'm not sure if this holds if an error occurs)
     * Note: Currently (1.12.'09) the SMT Solvers do not check if a node is FALSE.
     */
    public enum ThreeValuedTruth {
        VALID("valid"),
        FALSIFIABLE("there is a counter example"),
        UNKNOWN("unknown");

        private final String description;

        ThreeValuedTruth(String description) {
            this.description = description;
        }

        @Override
        public String toString() {
            return description;
        }
    }

    public static SMTValidResult getValidResult(SMTSolver solver, SMTProblem problem,
            long timeTaken, SolverCommunication solverCommunication) {
        return new SMTValidResult(solver, problem, timeTaken, solverCommunication);
    }

    public static SMTFalsifiableResult getFalsifiableResult(SMTSolver solver, SMTProblem problem,
            long timeTaken, SolverCommunication solverCommunication) {
        return new SMTFalsifiableResult(solver, problem, timeTaken, solverCommunication);
    }

    public static SMTCEResult getCEResult(SMTSolver solver, SMTProblem problem, long timeTaken,
            SolverCommunication solverCommunication, ModelExtractor query) {
        return new SMTCEResult(solver, problem, timeTaken, solverCommunication, query);
    }

    public static SMTUnknownResult getUnknownResult(SMTSolver solver, SMTProblem problem,
            long timeTaken, SolverCommunication solverCommunication) {
        return new SMTUnknownResult(solver, problem, timeTaken, solverCommunication);
    }

    public static SMTTimeoutResult getTimeoutResult(SMTSolver solver, SMTProblem problem,
            long timeTaken, SolverCommunication solverCommunication) {
        return new SMTTimeoutResult(solver, problem, timeTaken, solverCommunication);
    }

    public static SMTExceptionResult getExceptionResult(SMTSolver solver, SMTProblem problem,
            long timeTaken, SolverCommunication solverCommunication, Throwable exception) {
        return new SMTExceptionResult(solver, problem, timeTaken, solverCommunication, exception);
    }

    private SMTSolverResult(SMTSolver solver, SMTProblem problem, long timeTaken,
            SolverCommunication solverCommunication) {
        this.solver = solver;
        this.problem = problem;
        this.timeTaken = timeTaken;
        this.solverCommunication = solverCommunication;
    }

    public abstract ThreeValuedTruth isValid();

    public String getRawSolverOutput() {
        StringBuilder output = new StringBuilder();
        for (SolverCommunication.Message m : solverCommunication.getOutMessages()) {
            String s = m.content();
            output.append(s).append("\n");
        }
        return output.toString();
    }

    public String getRawSolverInput() {
        StringBuilder input = new StringBuilder();

        for (SolverCommunication.Message m : solverCommunication
                .getMessages(SolverCommunication.MessageType.INPUT)) {
            String s = m.content();
            input.append(s).append("\n");
        }
        return input.toString();
    }

    public SMTProblem getProblem() {
        return problem;
    }

    public long getTimeTaken() {
        return timeTaken;
    }

    public String getName() {
        return solver.name();
    }


    @Override
    public String toString() {
        return isValid().toString();
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof SMTSolverResult ssr)) {
            return false;
        }
        return isValid() == ssr.isValid();
    }


    public static class SMTValidResult extends SMTSolverResult {
        private SMTValidResult(SMTSolver solver, SMTProblem problem, long timeTaken,
                SolverCommunication solverCommunication) {
            super(solver, problem, timeTaken, solverCommunication);
        }

        @Override
        public ThreeValuedTruth isValid() {
            return ThreeValuedTruth.VALID;
        }
    }

    public static class SMTFalsifiableResult extends SMTSolverResult {
        private SMTFalsifiableResult(SMTSolver solver, SMTProblem problem, long timeTaken,
                SolverCommunication solverCommunication) {
            super(solver, problem, timeTaken, solverCommunication);
        }

        @Override
        public ThreeValuedTruth isValid() {
            return ThreeValuedTruth.FALSIFIABLE;
        }
    }

    public static class SMTCEResult extends SMTFalsifiableResult {
        private final ModelExtractor query;

        private SMTCEResult(SMTSolver solver, SMTProblem problem, long timeTaken,
                SolverCommunication solverCommunication, ModelExtractor query) {
            super(solver, problem, timeTaken, solverCommunication);
            this.query = query;
        }


        public ModelExtractor getQuery() {
            return query;
        }
    }

    public static class SMTUnknownResult extends SMTSolverResult {
        private SMTUnknownResult(SMTSolver solver, SMTProblem problem, long timeTaken,
                SolverCommunication solverCommunication) {
            super(solver, problem, timeTaken, solverCommunication);
        }

        @Override
        public ThreeValuedTruth isValid() {
            return ThreeValuedTruth.UNKNOWN;
        }
    }

    public static class SMTExceptionResult extends SMTUnknownResult {
        private final Throwable exception;

        private SMTExceptionResult(SMTSolver solver, SMTProblem problem, long timeTaken,
                SolverCommunication solverCommunication, Throwable exception) {
            super(solver, problem, timeTaken, solverCommunication);
            this.exception = exception;
        }

        public Throwable getException() {
            return exception;
        }
    }

    public static class SMTTimeoutResult extends SMTUnknownResult {
        private SMTTimeoutResult(SMTSolver solver, SMTProblem problem, long timeTaken,
                SolverCommunication solverCommunication) {
            super(solver, problem, timeTaken, solverCommunication);
        }
    }
}
