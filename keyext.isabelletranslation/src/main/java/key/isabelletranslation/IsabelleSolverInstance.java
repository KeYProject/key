package key.isabelletranslation;

import de.unruh.isabelle.control.Isabelle;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class IsabelleSolverInstance implements IsabelleSolver, Runnable {
    private SledgehammerResult result;

    private IsabelleResourceController.IsabelleResource isabelleResource;

    /**
     * The SMT problem that is related to this solver
     */
    private final IsabelleProblem problem;

    /**
     * It is possible that a solver has a listener.
     */
    private final IsabelleSolverListener listener;

    /**
     * The thread that is associated with this solver.
     */
    private Thread thread;

    /**
     * The timeout that is associated with this solver. Represents the timertask that is started
     * when the solver is started.
     */
    private IsabelleSolverTimeout solverTimeout;

    /**
     * stores the reason for interruption if present (e.g. User, Timeout, Exception)
     */
    private ReasonOfInterruption reasonOfInterruption = ReasonOfInterruption.NoInterruption;

    /**
     * the state the solver is currently in
     */
    private SolverState solverState = SolverState.Waiting;

    /**
     * Stores the settings that are used for the execution.
     */
    private IsabelleTranslationSettings isabelleSettings;

    /**
     * Stores the translation of the problem that is associated with this solver
     */
    private String problemString = "NOT YET COMPUTED";

    /**
     * If there was an exception while executing the solver it is stored in this attribute.
     */
    private Throwable exception;

    /**
     * The timeout in seconds for this SMT solver run.
     */
    private long timeout = -1;

    private IsabelleResourceController resourceController;


    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleSolver.class);

    public IsabelleSolverInstance(IsabelleProblem problem, IsabelleSolverListener listener, IsabelleResourceController resourceController) {
        this.problem = problem;
        this.listener = listener;
        this.resourceController = resourceController;
    }

    @Override
    public String name() {
        return "Isabelle";
    }

    @Override
    public String getTranslation() {
        return problem.getSequentTranslation();
    }

    @Override
    public IsabelleProblem getProblem() {
        return problem;
    }

    @Override
    public Throwable getException() {
        return exception;
    }

    @Override
    public void interrupt(ReasonOfInterruption reason) {
        setReasonOfInterruption(reason);
        setSolverState(SolverState.Stopped);
        if (solverTimeout != null) {
            solverTimeout.cancel();
        }
        if (thread != null) {
            thread.interrupt();
        }
    }

    private void setSolverState(SolverState solverState) {
            this.solverState = solverState;
    }

    public void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption) {
            this.reasonOfInterruption = reasonOfInterruption;
    }

    @Override
    public long getStartTime() {
        return 0;
    }

    @Override
    public long getTimeout() {
        return 0;
    }

    @Override
    public void setTimeout(long timeout) {

    }

    @Override
    public SolverState getState() {
        return null;
    }

    @Override
    public boolean wasInterrupted() {
        return false;
    }

    @Override
    public boolean isRunning() {
        return false;
    }

    @Override
    public void start(IsabelleSolverTimeout timeout, IsabelleTranslationSettings settings) {
        thread = new Thread(this, "IsabelleSolverInstance");
        this.solverTimeout = timeout;
        isabelleSettings = settings;
        thread.start();
    }

    @Override
    public void start(IsabelleSolverTimeout timeout, Isabelle isabelleInstance) {
        thread = new Thread(this, "IsabelleSolverInstance");
        isabelleResource = IsabelleResourceController.createIsabelleResourceFromInstance(isabelleInstance, isabelleSettings);
        this.solverTimeout = timeout;
        thread.start();
    }

    @Override
    public String getRawSolverOutput() {
        return problem.getResult().result().toString();
    }

    @Override
    public String getRawSolverInput() {
        return problem.getSequentTranslation();
    }

    @Override
    public SledgehammerResult getFinalResult() {
        return problem.getResult();
    }

    @Override
    public void run() {
        //Ensure there is an active IsabelleInstance
        setSolverState(SolverState.StartingIsabelle);
        listener.processStarted(problem);

    }
}
