package key.isabelletranslation;

import de.uka.ilkd.key.proof.Goal;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.*;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.*;
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
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class IsabelleProblem {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleProblem.class);
    private final Goal goal;
    private SledgehammerResult result = null;
    private final String preamble;
    private final String sequentTranslation;
    private final Collection<IsabelleSolverListener> listeners = new HashSet<>();

    public IsabelleProblem(Goal goal, String preamble, String sequentTranslation) {
        this.goal = goal;
        this.preamble = preamble;
        this.sequentTranslation = sequentTranslation;
    }

    public void addListener(IsabelleSolverListener listener) {
        listeners.add(listener);
    }

    public Goal getGoal() {
        return goal;
    }

    public String getSequentTranslation() {
        return sequentTranslation;
    }

    public String getPreamble() {
        return preamble;
    }

    public SledgehammerResult getResult() {
        return result;
    }

    public SledgehammerResult sledgehammer(long timeout_seconds) {
        LOGGER.debug("Starting Isabelle...");
        notifyProcessStarted();
        IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();

        Isabelle isabelle;
        ArrayList<Path> sessionRoots = new ArrayList<>();
        sessionRoots.add(settings.getTranslationPath());
        notifyBuildingStarted();
        try {
            Isabelle.Setup setup = JIsabelle.setupSetLogic("KeYTranslations",
                    JIsabelle.setupSetSessionRoots(sessionRoots,
                            JIsabelle.setupSetWorkingDirectory(settings.getTranslationPath(),
                                    JIsabelle.setup(settings.getIsabellePath()))));
            isabelle = new Isabelle(setup);
        } catch (Exception e) {
            LOGGER.error("Can't find Isabelle at {}", settings.getIsabellePath());
            notifyBuildingError(e);
            notifyProcessError(e);
            return null;
        }

        LOGGER.debug("Opening theory...");

        Theory thy0 = beginTheory(getSequentTranslation(), Path.of((settings.getTranslationPath() + "\\Translation.thy")), isabelle);
        ToplevelState toplevel = ToplevelState.apply(isabelle);
        notifyBuildingFinished();

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


        LOGGER.debug("Parsing theory...");
        notifyParsingStarted();
        try {
            java.util.List<Tuple2<Transition, String>> transitionsAndTexts = new ArrayList<>();
            parse_text.apply(thy0, getSequentTranslation(), isabelle,
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
            isabelle.destroy();
            notifyParsingError(e);
            return null;
        }
        notifyParsingFinished();
        LOGGER.debug("Finished Parsing");

        String Try = thy0.importMLStructureNow("Try0", isabelle);
        MLFunction<ToplevelState, Object> try_function =
                MLValue.compileFunction(
                        """
                                fn (state) =>
                                        let
                                            val p_state = Toplevel.proof_of state;
                                        in
                                           \s""" + Try + ".try0 (SOME (seconds 5.0)) ([], [], [], []) p_state" + """
                                        end
                                """, isabelle, Implicits.toplevelStateConverter(),
                        de.unruh.isabelle.mlvalue.Implicits.booleanConverter());

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
                                                [("timeout",\"""" + timeout_seconds + """
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
                                """ + timeout_seconds + ") go_run (state, thy) end", isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                        new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                        new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                        (new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter())))));

        Builder<String, List<String>> listBuilder = scala.collection.immutable.List.newBuilder();
        scala.collection.immutable.List<String> emptyList = listBuilder.result();

        SledgehammerResult result = null;
        SledgehammerResult tryResult = null;
        LOGGER.debug("Trying...");
        notifySledgehammerStarted();
        try {
            Future<Tuple2<Object, Tuple2<String, List<String>>>> resultFuture = normal_with_Sledgehammer.apply(toplevel, thy0, emptyList, emptyList, isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))
                    .retrieve(new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))), isabelle);
            Future<Object> tryResultSuccessF = try_function.apply(toplevel, isabelle, Implicits.toplevelStateConverter())
                    .retrieve(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), isabelle);
            Boolean tryResultSuccess = false;
            try {
                tryResultSuccess = (Boolean) Await.result(tryResultSuccessF, Duration.create(timeout_seconds, TimeUnit.SECONDS));
            } catch (TimeoutException e) {
                tryResultSuccess = false;
            }
            if (tryResultSuccess) {
                tryResult = new SledgehammerResult(Option.apply(new Tuple2<>("some", "try0")));
                this.result = tryResult;
                notifySledgehammerFinished();
                notifyProcessFinished();
                LOGGER.debug("Sledgehammer result: " + this.result);
                return this.result;
            }
            Tuple2<Object, Tuple2<String, List<String>>> resultFutureCollect = Await.result(resultFuture, Duration.create(timeout_seconds, TimeUnit.SECONDS));
            result = new SledgehammerResult(Option.apply(new Tuple2<>(resultFutureCollect._2()._1(), resultFutureCollect._2()._2().head())));
            this.result = result;
        } catch (TimeoutException exception) {
            result = new SledgehammerResult(Option.apply(new Tuple2<>("timeout", "timeout")));
            this.result = result;
            notifyProcessTimeout();
        } catch (InterruptedException exception) {
            result = new SledgehammerResult(Option.apply(null));
            this.result = result;
            notifySledgehammerError(exception);
            notifyProcessError(exception);
        } catch (Exception exception) {
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
        } finally {
            isabelle.destroy();
        }

        notifySledgehammerFinished();

        notifyProcessFinished();

        LOGGER.debug("Sledgehammer result: " + this.result);
        return this.result;
    }

    protected SledgehammerResult try0ThenSledgehammer(Isabelle isabelle, Theory thy0, long timeout_seconds) {
        notifyProcessStarted();
        ToplevelState toplevel = ToplevelState.apply(isabelle);

        MLFunction2<Theory, String, List<Tuple2<Transition, String>>> parse_text = MLValue.compileFunction("""
                fn (thy, text) => let
                val transitions = Outer_Syntax.parse_text thy (K thy) Position.start text
                fun addtext symbols [tr] =
                      [(tr, implode symbols)]
                  | addtext _ [] = []
                  | addtext symbols (tr::nextTr::trs) = let
                      val (this,rest) = Library.chop (Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of nextTr) |> Option.valOf) symbols
                      in (tr, implode this) :: addtext rest (nextTr::trs) end
                in addtext (Symbol.explode text) transitions end""", isabelle, Implicits.theoryConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(new Tuple2Converter<>(Implicits.transitionConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())));

        MLFunction3<Object, Transition, ToplevelState, ToplevelState> command_exception = MLValue.compileFunction("fn (int, tr, st) => Toplevel.command_exception int tr st", isabelle, de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter(), Implicits.toplevelStateConverter());


        LOGGER.debug("Parsing theory...");
        notifyParsingStarted();
        try {
            java.util.List<Tuple2<Transition, String>> transitionsAndTexts = new ArrayList<>();
            parse_text.apply(thy0, getSequentTranslation(), isabelle, Implicits.theoryConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter()).retrieveNow(new ListConverter<>(new Tuple2Converter<>(Implicits.transitionConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())), isabelle).foreach(transitionsAndTexts::add);

            for (Tuple2<Transition, String> transitionAndText : transitionsAndTexts) {
                //println(s"""Transition: "${text.strip}"""")
                toplevel = command_exception.apply(Boolean.TRUE, transitionAndText._1(), toplevel, isabelle, de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter()).retrieveNow(Implicits.toplevelStateConverter(), isabelle);
            }
        } catch (Exception e) {
            notifyParsingError(e);
            return null;
        }
        notifyParsingFinished();
        LOGGER.debug("Finished Parsing");

        String Try = thy0.importMLStructureNow("Try0", isabelle);
        MLFunction<ToplevelState, Object> try_function = MLValue.compileFunction("""
                fn (state) =>
                        let
                            val p_state = Toplevel.proof_of state;
                        in
                           \s""" + Try + ".try0 (SOME (seconds 5.0)) ([], [], [], []) p_state" + """
                        end
                """, isabelle, Implicits.toplevelStateConverter(), de.unruh.isabelle.mlvalue.Implicits.booleanConverter());

        String sledgehammer = thy0.importMLStructureNow("Sledgehammer", isabelle);
        String Sledgehammer_Commands = thy0.importMLStructureNow("Sledgehammer_Commands", isabelle);
        String Sledgehammer_Prover = thy0.importMLStructureNow("Sledgehammer_Prover", isabelle);

        MLFunction4<ToplevelState, Theory, scala.collection.immutable.List<String>, scala.collection.immutable.List<String>, Tuple2<Object, Tuple2<String, scala.collection.immutable.List<String>>>> normal_with_Sledgehammer = MLValue.compileFunction("""
                fn (state, thy, adds, dels) =>
                  let
                     val override = {add=[],del=[],only=false};
                     fun go_run (state, thy) =
                        let
                           val p_state = Toplevel.proof_of state;
                           val ctxt = Proof.context_of p_state;
                           val params =\s""" + Sledgehammer_Commands + """
                .default_params thy
                                [("timeout",\"""" + (timeout_seconds) + """
                "),("verbose","true"),("provers", "cvc4 verit z3 e spass vampire zipperposition")];
                val results =\s""" + sledgehammer + """
                .run_sledgehammer params\s""" + Sledgehammer_Prover + """
                .Normal NONE 1 override p_state;
                             val (result, (outcome, step)) = results;
                           in
                             (result, (""" + sledgehammer + """
                .short_string_of_sledgehammer_outcome outcome, [YXML.content_of step]))
                           end;
                    in
                      Timeout.apply (Time.fromSeconds\s
                """ + (timeout_seconds + 100) + ") go_run (state, thy) end", isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()), (new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter())))));

        Builder<String, List<String>> listBuilder = scala.collection.immutable.List.newBuilder();
        scala.collection.immutable.List<String> emptyList = listBuilder.result();

        SledgehammerResult result = null;
        SledgehammerResult tryResult = null;
        LOGGER.debug("Trying...");
        notifySledgehammerStarted();
        try {
            Future<Tuple2<Object, Tuple2<String, List<String>>>> resultFuture = normal_with_Sledgehammer.apply(toplevel, thy0, emptyList, emptyList, isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter())).retrieve(new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))), isabelle);
            Future<Object> tryResultSuccessF = try_function.apply(toplevel, isabelle, Implicits.toplevelStateConverter())
                    .retrieve(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), isabelle);
            Boolean tryResultSuccess;
            try {
                tryResultSuccess = (Boolean) Await.result(tryResultSuccessF, Duration.create(timeout_seconds, TimeUnit.SECONDS));
            } catch (TimeoutException e) {
                tryResultSuccess = false;
            }
            if (tryResultSuccess) {
                tryResult = new SledgehammerResult(Option.apply(new Tuple2<>("some", "try0")));
                this.result = tryResult;
                notifySledgehammerFinished();
                notifyProcessFinished();
                LOGGER.debug("Sledgehammer result: " + this.result);
                return this.result;
            }
            Tuple2<Object, Tuple2<String, List<String>>> resultFutureCollect = Await.result(resultFuture, Duration.create(timeout_seconds, TimeUnit.SECONDS));
            result = new SledgehammerResult(Option.apply(new Tuple2<>(resultFutureCollect._2()._1(), resultFutureCollect._2()._2().head())));
            this.result = result;
        } catch (TimeoutException exception) {
            result = new SledgehammerResult(Option.apply(new Tuple2<>("timeout", "timeout")));
            this.result = result;
            notifyProcessTimeout();
        } catch (InterruptedException exception) {
            result = new SledgehammerResult(Option.apply(null));
            this.result = result;
            notifySledgehammerError(exception);
            notifyProcessError(exception);
        } catch (Exception exception) {
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

        if (result.isTimeout()) {
            notifyProcessTimeout();
        }

        notifySledgehammerFinished();

        notifyProcessFinished();


        LOGGER.debug("Sledgehammer result: " + this.result);
        return this.result;
    }

    private Theory beginTheory(String thyText, Path source, Isabelle isabelle) {
        MLFunction3<Path, TheoryHeader, scala.collection.immutable.List<Theory>, Theory> begin_theory =
                MLValue.compileFunction("fn (path, header, parents) => Resources.begin_theory path header parents", isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()), Implicits.theoryConverter());
        MLFunction2<String, Position, TheoryHeader> header_read = MLValue.compileFunction("fn (text,pos) => Thy_Header.read pos text", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter(), Implicits.theoryHeaderConverter());

        TheoryHeader header = header_read.apply(thyText, Position.none(isabelle), isabelle, de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter())
                .retrieveNow(Implicits.theoryHeaderConverter(), isabelle);
        Path topDir = source.getParent();
        return begin_theory.apply(topDir, header, header.imports(isabelle).map((String name) -> Theory.apply(name, isabelle)), isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()))
                .retrieveNow(Implicits.theoryConverter(), isabelle);
    }


    private void notifyParsingStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.parsingStarted(this);
        }
    }

    private void notifyParsingFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.parsingFinished(this);
        }
    }

    private void notifyParsingError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.parsingFailed(this, e);
        }
    }

    private void notifyBuildingStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.buildingStarted(this);
        }
    }

    private void notifyBuildingFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.buildingFinished(this);
        }
    }

    private void notifyBuildingError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.buildingFailed(this, e);
        }
    }

    private void notifyProcessStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.processStarted(this);
        }
    }

    private void notifyProcessFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.processStopped(this);
        }
    }

    private void notifyProcessError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.processInterrupted(this, e);
        }
    }

    private void notifyProcessTimeout() {
        for (IsabelleSolverListener listener : listeners) {
            listener.processTimeout(this);
        }
    }

    private void notifySledgehammerStarted() {
        for (IsabelleSolverListener listener : listeners) {
            listener.sledgehammerStarted(this);
        }
    }

    private void notifySledgehammerFinished() {
        for (IsabelleSolverListener listener : listeners) {
            listener.sledgehammerFinished(this);
        }
    }

    private void notifySledgehammerError(Exception e) {
        for (IsabelleSolverListener listener : listeners) {
            listener.sledgehammerFailed(this, e);
        }
    }

    public void removeListener(IsabelleSolverListener listener) {
        listeners.remove(listener);
    }
}