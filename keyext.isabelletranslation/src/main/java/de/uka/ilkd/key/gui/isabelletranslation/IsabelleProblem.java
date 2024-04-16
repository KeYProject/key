package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.proof.Goal;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.*;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.Tuple2;
import scala.collection.immutable.List;
import scala.collection.mutable.Builder;

import java.nio.file.Path;
import java.util.ArrayList;

public class IsabelleProblem {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleProblem.class);
    private final Goal goal;
    private SledgehammerResult result = null;
    private final String preamble;
    private final String sequentTranslation;

    public IsabelleProblem(Goal goal, String preamble, String sequentTranslation) {
        this.goal = goal;
        this.preamble = preamble;
        this.sequentTranslation = sequentTranslation;
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

    public SledgehammerResult sledgehammer() {
        LOGGER.info("Starting Isabelle...");
        IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();

        Isabelle isabelle;
        ArrayList<Path> sessionRoots = new ArrayList<>();
        sessionRoots.add(settings.getTranslationPath());
        try {
            Isabelle.Setup setup = JIsabelle.setupSetLogic("KeYTranslations",
                    JIsabelle.setupSetSessionRoots(sessionRoots,
                            JIsabelle.setupSetWorkingDirectory(settings.getTranslationPath(),
                                    JIsabelle.setup(settings.getIsabellePath()))));
            isabelle = new Isabelle(setup);
        } catch (Exception e) {
            LOGGER.error("Can't find Isabelle at {}", settings.getIsabellePath());
            return null;
        }

        LOGGER.info("Opening theory...");

        Theory thy0 = beginTheory(getSequentTranslation(), Path.of((settings.getTranslationPath() + "\\Translation.thy")), isabelle);
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
                        in addtext (Symbol.explode text) transitions end""", isabelle,
                Implicits.theoryConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(new Tuple2Converter<>(Implicits.transitionConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())));

        MLFunction3<Object, Transition, ToplevelState, ToplevelState> command_exception = MLValue.compileFunction("fn (int, tr, st) => Toplevel.command_exception int tr st", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter(), Implicits.toplevelStateConverter());


        LOGGER.info("Parsing theory...");
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
        LOGGER.info("Finished Parsing");

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
                                                [("timeout","30"),("verbose","true")];
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
                                      Timeout.apply (Time.fromSeconds 35) go_run (state, thy) end
                                """, isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                        new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                        new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                        (new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter())))));

        Builder<String, List<String>> listBuilder = scala.collection.immutable.List.newBuilder();
        scala.collection.immutable.List<String> emptyList = listBuilder.result();

        SledgehammerResult result;
        LOGGER.info("Sledgehammering...");
        try {
            result = new SledgehammerResult(normal_with_Sledgehammer.apply(toplevel, thy0, emptyList, emptyList, isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                            new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))
                    .retrieveNow(new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))), isabelle));
        } catch (Exception exception) {
            result = new SledgehammerResult(new Tuple2<>(Boolean.FALSE, new Tuple2<>("", emptyList)));
        }
        isabelle.destroy();

        LOGGER.info("Sledgehammer result: " + result);
        return this.result = result;
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
}
