package org.key_project.isabelletranslation.automation;

import java.time.Duration;
import java.time.Instant;
import java.util.concurrent.Callable;

public interface IsabelleSolver extends Callable<IsabelleResult> {
    int getSolverIndex();

    ReasonOfInterruption getReasonOfInterruption();

    enum ReasonOfInterruption {
        User, NoInterruption
    }

    enum SolverState{
        Waiting, Preparing, Parsing, Running, Stopped
    }

    String name();

    String getTranslation();

    IsabelleProblem getProblem();

    Throwable getException();

    void interrupt(ReasonOfInterruption reason);

    Instant getStartTime();

    Duration getComputationTime();

    int getTimeout();

    void setTimeout(int timeout);

    SolverState getState();

    boolean isRunning();

    String getRawSolverOutput();

    String getRawSolverInput();

    IsabelleResult getFinalResult();

}
