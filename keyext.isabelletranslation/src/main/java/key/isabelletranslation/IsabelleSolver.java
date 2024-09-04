package key.isabelletranslation;

import de.unruh.isabelle.control.Isabelle;

import java.util.TimerTask;

public interface IsabelleSolver {
    int getSolverIndex();

    ReasonOfInterruption getReasonOfInterruption();

    enum ReasonOfInterruption {
        User, Timeout, Exception, NoInterruption
    }

    enum SolverState{
        Waiting, Preparing, Parsing, Running, Stopped
    }

    String name();

    String getTranslation();

    IsabelleProblem getProblem();

    Throwable getException();

    void interrupt(ReasonOfInterruption reason);

    long getStartTime();

    long getTimeout();

    void setTimeout(long timeout);

    SolverState getState();

    boolean wasInterrupted();

    boolean isRunning();

    void start(IsabelleSolverTimeout timeout, IsabelleTranslationSettings settings);

    String getRawSolverOutput();

    String getRawSolverInput();

    SledgehammerResult getFinalResult();


        class IsabelleSolverTimeout extends TimerTask {
            private final IsabelleSolver solver;

            public IsabelleSolverTimeout(IsabelleSolver solver) {
                this.solver = solver;
            }

            @Override
            public void run() {
                solver.interrupt(ReasonOfInterruption.Timeout);
            }
        }

}
