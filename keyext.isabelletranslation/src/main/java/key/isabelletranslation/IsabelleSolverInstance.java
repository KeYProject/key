package key.isabelletranslation;

import com.sun.java.accessibility.util.TopLevelWindowListener;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Constraint;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.*;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.Theory;
import de.unruh.isabelle.pure.ToplevelState;
import de.unruh.isabelle.pure.Transition;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.Option;
import scala.Tuple2;
import scala.collection.immutable.List;
import scala.collection.mutable.Builder;
import scala.concurrent.Await;
import scala.concurrent.Future;
import scala.concurrent.duration.Duration;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Timer;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class IsabelleSolverInstance implements IsabelleSolver, Runnable {
    private SledgehammerResult result;

    private IsabelleResourceController.IsabelleResource isabelleResource;

    /**
     * The SMT problem that is related to this solver
     */
    private final IsabelleProblem problem;

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
    private Collection<IsabelleSolverListener> listeners;

    public IsabelleSolverInstance(IsabelleProblem problem, Collection<IsabelleSolverListener> listeners, IsabelleResourceController resourceController) {
        this.problem = problem;
        this.listeners = new HashSet<>();
        this.listeners.addAll(listeners);
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
        if (isabelleResource != null) {
            shutdownAndReturnResource();
        }
    }

    private void shutdownAndReturnResource() {
        isabelleResource.interrupt();
        resourceController.returnResource(this, isabelleResource);
    }

    private void setSolverState(SolverState solverState) {
            this.solverState = solverState;
    }

    public void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption) {
            this.reasonOfInterruption = reasonOfInterruption;
    }

    @Override
    public long getStartTime() {
        if (solverTimeout == null) {
            return -1;
        }
        return solverTimeout.scheduledExecutionTime();
    }

    @Override
    public long getTimeout() {
        return this.timeout;
    }

    @Override
    public void setTimeout(long timeout) {
        this.timeout = timeout;
    }

    @Override
    public SolverState getState() {
        return solverState;
    }

    @Override
    public boolean wasInterrupted() {
        return reasonOfInterruption != ReasonOfInterruption.NoInterruption;
    }

    @Override
    public boolean isRunning() {
        return solverState == SolverState.Running;
    }

    @Override
    public void start(IsabelleSolverTimeout timeout, IsabelleTranslationSettings settings) {
        thread = new Thread(this, "IsabelleSolverInstance");
        this.solverTimeout = timeout;
        isabelleSettings = settings;

        //TODO probably want asynchronous behavior
        //Thread.start();
        run();
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
        notifyProcessStarted();

        try {
            isabelleResource = resourceController.getIsabelleResource(this);
        } catch (InterruptedException e) {
            this.interrupt(ReasonOfInterruption.Exception);
            notifyProcessError(e);
        }

        Isabelle isabelle = isabelleResource.instance();
        Theory thy0 = isabelleResource.theory();

        MLFunction2<Theory, String, List<Tuple2<Transition, String>>> parse_text = MLValue.compileFunction("""
                        fn (thy, text) => let
                        val transitions = Outer_Syntax.parse_text thy (K thy) Position.start text
                        fun addtext symbols [tr] =
                              [(tr, implode symbols)]
                          | addtext _ [] = []
                          | addtext symbols (tr::nextTr::trs) = let
                              val (this,rest) = Library.chop (Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of nextTr) |> Option.valOf) symbols
                              in (tr, implode this) :: addtext rest (nextTr::trs) end
                        in addtext (Symbol.explode text) transitions end""", isabelle,
                Implicits.theoryConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(new Tuple2Converter<>(Implicits.transitionConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())));

        MLFunction3<Object, Transition, ToplevelState, ToplevelState> command_exception = MLValue.compileFunction("fn (int, tr, st) => Toplevel.command_exception int tr st", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter(), Implicits.toplevelStateConverter());


        ToplevelState toplevel = ToplevelState.apply(isabelle);
        LOGGER.debug("Parsing theory...");
        notifyParsingStarted();
        try {
            java.util.List<Tuple2<Transition, String>> transitionsAndTexts = new ArrayList<>();
            parse_text.apply(thy0, getProblem().getSequentTranslation(), isabelle,
                            Implicits.theoryConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())
                    .retrieveNow(new ListConverter<>(new Tuple2Converter<>(Implicits.transitionConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())), isabelle)
                    .foreach(transitionsAndTexts::add);

            for (Tuple2<Transition, String> transitionAndText : transitionsAndTexts) {
                //println(s"""Transition: "${text.strip}"""")
                toplevel = command_exception.apply(Boolean.TRUE, transitionAndText._1(), toplevel, isabelle,
                                de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter())
                        .retrieveNow(Implicits.toplevelStateConverter(), isabelle);
            }
        } catch (Exception e) {
            isabelleResource.destroy();
            notifyParsingError(e);
            return;
        }
        notifyParsingFinished();
        LOGGER.debug("Finished Parsing");

        String sledgehammer = thy0.importMLStructureNow("Sledgehammer", isabelle);
        String Sledgehammer_Commands = thy0.importMLStructureNow("Sledgehammer_Commands", isabelle);
        String Sledgehammer_Prover = thy0.importMLStructureNow("Sledgehammer_Prover", isabelle);

        MLFunction4<ToplevelState, Theory, scala.collection.immutable.List<String>, scala.collection.immutable.List<String>, Tuple2<Object, Tuple2<String, scala.collection.immutable.List<String>>>> normal_with_Sledgehammer =
                MLValue.compileFunction(
                        """
                                fn (state, thy, adds, dels) =>
                                  let
                                     val override = {add=[],del=[],only=false};
                                     fun go_run (state, thy) =
                                        let
                                           val p_state = Toplevel.proof_of state;
                                           val ctxt = Proof.context_of p_state;
                                           val params =\s""" + Sledgehammer_Commands + """
                                .default_params thy
                                                [("timeout",\"""" + getTimeout() + """
                                "),("verbose","true"),("provers", "cvc4 verit z3 e spass vampire zipperposition")];
                                val results =\s"""
                                + sledgehammer + """
                                .run_sledgehammer params\s""" + Sledgehammer_Prover + """
                                .Normal NONE 1 override p_state;
                                             val (result, (outcome, step)) = results;
                                           in
                                             (result, (""" + sledgehammer + """
                                .short_string_of_sledgehammer_outcome outcome, [YXML.content_of step]))
                                           end;
                                    in
                                      Timeout.apply (Time.fromSeconds\s
                                """ + getTimeout() + ") go_run (state, thy) end", isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                        new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                        new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                        (new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter())))));

        Builder<String, List<String>> listBuilder = scala.collection.immutable.List.newBuilder();
        scala.collection.immutable.List<String> emptyList = listBuilder.result();

        SledgehammerResult result = null;
        notifySledgehammerStarted();
        try {
            Future<Tuple2<Object, Tuple2<String, List<String>>>> resultFuture = normal_with_Sledgehammer.apply(toplevel, thy0, emptyList, emptyList, isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))
                    .retrieve(new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))), isabelle);
            Tuple2<Object, Tuple2<String, List<String>>> resultFutureCollect = Await.result(resultFuture, Duration.create(getTimeout(), TimeUnit.SECONDS));
            result = new SledgehammerResult(Option.apply(new Tuple2<>(resultFutureCollect._2()._1(), resultFutureCollect._2()._2().head())));
            this.result = result;
        } catch (TimeoutException exception) {
            interrupt(ReasonOfInterruption.Timeout);
            result = new SledgehammerResult(Option.apply(new Tuple2<>("timeout", "timeout")));
            this.result = result;
            notifyProcessTimeout();
        } catch (InterruptedException exception) {
            interrupt(ReasonOfInterruption.Exception);
            result = new SledgehammerResult(Option.apply(null));
            this.result = result;
            notifySledgehammerError(exception);
            notifyProcessError(exception);
        } catch (Exception exception) {
            interrupt(ReasonOfInterruption.Exception);
            if (exception.getMessage().contains("Timeout after")) {
                result = new SledgehammerResult(Option.apply(new Tuple2<>("timeout", "timeout")));
                this.result = result;
                notifyProcessTimeout();
            } else {
                LOGGER.error("Exception during Sledgehammer {}", exception.getMessage());
                exception.printStackTrace();
                result = new SledgehammerResult(Option.apply(null));
                this.result = result;
                notifySledgehammerError(exception);
                notifyProcessError(exception);
            }
        }
        getProblem().setResult(this.result);
        resourceController.returnResource(this, isabelleResource);
        notifySledgehammerFinished();

        notifyProcessFinished();

        LOGGER.debug("Sledgehammer result: " + this.result);
    }



    private void notifyParsingStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.parsingStarted(this, getProblem());
        }
    }

    private void notifyParsingFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.parsingFinished(this, getProblem());
        }
    }

    private void notifyParsingError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.parsingFailed(this, getProblem(), e);
        }
    }

    private void notifyBuildingStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.buildingStarted(this, getProblem());
        }
    }

    private void notifyBuildingFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.buildingFinished(this, getProblem());
        }
    }

    private void notifyBuildingError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.buildingFailed(this, getProblem(), e);
        }
    }

    private void notifyProcessStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.processStarted(this, getProblem());
        }
    }

    private void notifyProcessFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.processStopped(this, getProblem());
        }
    }

    private void notifyProcessError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.processInterrupted(this, getProblem(), e);
        }
    }

    private void notifyProcessTimeout() {
        for (IsabelleSolverListener listener : listeners) {
            listener.processTimeout(this, getProblem());
        }
    }

    private void notifySledgehammerStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.sledgehammerStarted(this, getProblem());
        }
    }

    private void notifySledgehammerFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.sledgehammerFinished(this, getProblem());
        }
    }

    private void notifySledgehammerError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.sledgehammerFailed(this, getProblem(), e);
        }
    }

    public void removeListener(IsabelleSolverListener listener) {
        listeners.remove(listener);
    }
}
