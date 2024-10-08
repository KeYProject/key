package org.key_project.isabelletranslation;

import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.control.IsabelleMLException;
import de.unruh.isabelle.mlvalue.*;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.Theory;
import de.unruh.isabelle.pure.ToplevelState;
import de.unruh.isabelle.pure.Transition;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.Tuple2;
import scala.collection.immutable.List;
import scala.collection.mutable.Builder;
import scala.concurrent.Await;
import scala.concurrent.Future;
import scala.concurrent.duration.Duration;

import java.time.Instant;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class IsabelleSledgehammerSolver implements IsabelleSolver {
    private final int solverIndex;
    private IsabelleResult result;

    private IsabelleResourceController.IsabelleResource isabelleResource;

    /**
     * The SMT problem that is related to this solver
     */
    private final IsabelleProblem problem;

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
    private final IsabelleTranslationSettings isabelleSettings;

    /**
     * If there was an exception while executing the solver it is stored in this attribute.
     */
    private Throwable exception;

    /**
     * The timeout in seconds for this SMT solver run.
     */
    private int timeout;

    private Instant startTime;

    private java.time.Duration computationTime;

    private final IsabelleResourceController resourceController;


    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleSledgehammerSolver.class);
    private final Collection<IsabelleSolverListener> listeners;

    public IsabelleSledgehammerSolver(IsabelleProblem problem, Collection<IsabelleSolverListener> listeners, int solverIndex, IsabelleResourceController resourceController, IsabelleTranslationSettings settings) {
        this.problem = problem;
        this.solverIndex = solverIndex;
        this.listeners = new HashSet<>();
        this.listeners.addAll(listeners);
        this.resourceController = resourceController;
        this.isabelleSettings = settings;
        this.timeout = isabelleSettings.getTimeout();
    }

    @Override
    public int getSolverIndex() {
        return solverIndex;
    }

    @Override
    public ReasonOfInterruption getReasonOfInterruption() {
        return reasonOfInterruption;
    }

    @Override
    public String name() {
        return "Isabelle Solver: " + problem.getName();
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
        this.result = IsabelleResult.getInterruptedResult();
        if (isabelleResource != null) {
            returnResource();
        }
        setSolverState(SolverState.Stopped);
    }

    private void returnResource() {
        if (isabelleResource == null) {
            return;
        }
        resourceController.returnResource(this, isabelleResource);
        isabelleResource = null;
    }

    private void setSolverState(SolverState solverState) {
            this.solverState = solverState;
    }

    public void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption) {
            this.reasonOfInterruption = reasonOfInterruption;
    }

    @Override
    public Instant getStartTime() {
        return startTime;
    }

    @Override
    public int getTimeout() {
        return this.timeout;
    }

    @Override
    public void setTimeout(int timeout) {
        this.timeout = timeout;
    }

    @Override
    public SolverState getState() {
        return solverState;
    }

    @Override
    public boolean isRunning() {
        return solverState == SolverState.Running;
    }

    @Override
    public String getRawSolverOutput() {
        return result.getSuccessfulTactic();
    }

    @Override
    public String getRawSolverInput() {
        return problem.getSequentTranslation();
    }

    @Override
    public IsabelleResult getFinalResult() {
        return this.result;
    }


    @Override
    public IsabelleResult call() throws InterruptedException {
        //Ensure there is an active IsabelleInstance
        setSolverState(SolverState.Preparing);
        try {
            isabelleResource = resourceController.getIsabelleResource(this);
        } catch (InterruptedException e) {
            return handleInterrupt();
        }


        notifyProcessStarted();
        startTime = Instant.now();
        Isabelle isabelle = isabelleResource.instance();


        LOGGER.info("Parsing theory for: {}", problem.getName());
        setSolverState(SolverState.Parsing);
        ToplevelState toplevel = ToplevelState.apply(isabelle);
        try {
            toplevel = parseTheory(toplevel, isabelleResource);
        } catch (InterruptedException e) {
            return handleInterrupt();
        } catch (IsabelleMLException e) {
            return handleIsabelleError(e);
        }
        LOGGER.info("Finished Parsing");


        setSolverState(SolverState.Running);
        try {
            this.result = sledgehammer(isabelleResource, toplevel);
            computationTime = java.time.Duration.between(startTime, Instant.now());
        } catch (TimeoutException e) {
            this.result = IsabelleResult.getTimeoutResult(computationTime);
            computationTime = java.time.Duration.between(startTime, Instant.now());
        } catch (InterruptedException e) {
            return handleInterrupt();
        } catch (IsabelleMLException e) {
            return handleIsabelleError(e);
        }
        LOGGER.info("Sledgehammer result: {}", this.result.getDescription());
        returnResource();
        setSolverState(SolverState.Stopped);
        notifyProcessFinished();
        return this.result;
    }

    private ToplevelState parseTheory(ToplevelState toplevel, IsabelleResourceController.IsabelleResource resource) throws InterruptedException, IsabelleMLException {
        ToplevelState result = toplevel;
        Isabelle isabelle = resource.instance();
        Theory thy0 = resource.theory();

        if (Thread.currentThread().isInterrupted()) {
            throw new InterruptedException();
        }
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

        if (Thread.currentThread().isInterrupted()) {
            throw new InterruptedException();
        }
        MLFunction3<Object, Transition, ToplevelState, ToplevelState> command_exception = MLValue.compileFunction("fn (int, tr, st) => Toplevel.command_exception int tr st", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter(), Implicits.toplevelStateConverter());

        java.util.List<Tuple2<Transition, String>> transitionsAndTexts = new ArrayList<>();
        List<Tuple2<Transition, String>> transitionList = parse_text.apply(thy0, getProblem().getSequentTranslation(), isabelle,
                        Implicits.theoryConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())
                .retrieveNow(new ListConverter<>(new Tuple2Converter<>(Implicits.transitionConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())), isabelle);
        transitionList.foreach(transitionsAndTexts::add);

        for (Tuple2<Transition, String> transitionAndText : transitionsAndTexts) {
            //println(s"""Transition: "${text.strip}"""")
            if (Thread.currentThread().isInterrupted()) {
                throw new InterruptedException();
            }
            result = command_exception.apply(Boolean.TRUE, transitionAndText._1(), result, isabelle,
                            de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter())
                        .retrieveNow(Implicits.toplevelStateConverter(), isabelle);
        }
        return result;
    }


    private IsabelleResult sledgehammer(IsabelleResourceController.IsabelleResource resource, ToplevelState toplevel)
                throws TimeoutException, InterruptedException, IsabelleMLException {
        Isabelle isabelle = resource.instance();
        Theory thy0 = resource.theory();

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
                                                [("timeout",\"""" + (double) timeout + """
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

        IsabelleResult result;
        Future<Tuple2<Object, Tuple2<String, List<String>>>> resultFuture = normal_with_Sledgehammer.apply(toplevel, thy0, emptyList, emptyList, isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))
                    .retrieve(new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))), isabelle);
        Tuple2<Object, Tuple2<String, List<String>>> resultFutureCollect = Await.result(resultFuture, Duration.create(getTimeout(), TimeUnit.SECONDS));

        boolean successful = (boolean) resultFutureCollect._1();

        if (successful) {
            result = IsabelleResult.getSuccessResult(resultFutureCollect._2()._2().head(), computationTime);
        } else {
            result = IsabelleResult.getUnknownResult();
        }
        this.result = result;
        return this.result;
    }

    private IsabelleResult handleInterrupt() {
        this.result = IsabelleResult.getInterruptedResult();
        returnResource();
        Thread.currentThread().interrupt();
        setSolverState(SolverState.Stopped);
        notifyProcessError(new InterruptedException());
        return this.result;
    }

    private IsabelleResult handleIsabelleError(Exception e) {
        this.result = IsabelleResult.getErrorResult(e);
        this.exception = e;
        returnResource();
        setSolverState(SolverState.Stopped);
        notifyProcessError(e);
        return this.result;
    }

    @Override
    public java.time.Duration getComputationTime() {
        return computationTime;
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
            listener.processError(this, getProblem(), e);
        }
    }
}
