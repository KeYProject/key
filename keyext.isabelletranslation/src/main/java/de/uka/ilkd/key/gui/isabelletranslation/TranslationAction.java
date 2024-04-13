package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTRuleApp;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.*;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.Tuple2;
import scala.collection.mutable.Builder;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

public class TranslationAction extends MainWindowAction {

    private static final Logger LOGGER = LoggerFactory.getLogger(TranslationAction.class);

    public TranslationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translation Action");

        generateTranslation();
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

    private void generateTranslation() {
        KeYMediator mediator = getMediator();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());
        try {
            //TODO let user choose where to save file?
            File translationFile = new File(System.getProperty("user.home") + "/.key/IsabelleTranslations/Translation.thy");
            StringBuilder translation = translator.translateProblem(mediator.getSelectedGoal().sequent());

            //TODO find Isabelle path
            Isabelle.Setup setup = JIsabelle.setup(Path.of("C:\\Users\\Nils\\Documents\\Isabelle2023"));
            Isabelle isabelle = new Isabelle(setup);
            //TODO automatically run try/sledgehammer instead of opening Isabelle
            List<Path> filePaths = new ArrayList<>();


            Theory thy0 = beginTheory(translation.toString(), translationFile.toPath(), isabelle);
            ToplevelState toplevel = ToplevelState.apply(isabelle);

            MLFunction2<Theory, String, scala.collection.immutable.List<Tuple2<Transition, String>>> parse_text = MLValue.compileFunction("""
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

            List<Tuple2<Transition, String>> transitionsAndTexts = new ArrayList<>();
            parse_text.apply(thy0, translation.toString(), isabelle,
                            Implicits.theoryConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())
                    .retrieveNow(new ListConverter<>(new Tuple2Converter<>(Implicits.transitionConverter(), de.unruh.isabelle.mlvalue.Implicits.stringConverter())), isabelle)
                    .foreach(transitionsAndTexts::add);

            for (Tuple2<Transition, String> transitionAndText : transitionsAndTexts) {
                //println(s"""Transition: "${text.strip}"""")
                toplevel = command_exception.apply(Boolean.TRUE, transitionAndText._1(), toplevel, isabelle,
                                de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), Implicits.transitionConverter(), Implicits.toplevelStateConverter())
                        .retrieveNow(Implicits.toplevelStateConverter(), isabelle);
            }

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

            Builder<String, scala.collection.immutable.List<String>> listBuilder = scala.collection.immutable.List.newBuilder();
            scala.collection.immutable.List<String> emptyList = listBuilder.result();

            Tuple2<Object, Tuple2<String, scala.collection.immutable.List<String>>> result;
            LOGGER.info("Sledgehammering...");
            try {
                result = normal_with_Sledgehammer.apply(toplevel, thy0, emptyList, emptyList, isabelle, Implicits.toplevelStateConverter(), Implicits.theoryConverter(),
                                new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()),
                                new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))
                        .retrieveNow(new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.booleanConverter(), new Tuple2Converter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter(), new ListConverter<>(de.unruh.isabelle.mlvalue.Implicits.stringConverter()))), isabelle);
            } catch (Exception exception) {
                result = new Tuple2<>(Boolean.FALSE, new Tuple2<>("", emptyList));
            }
            LOGGER.info("Sledgehammer result: " + result);

            //TODO needs its own action to enable undo, etc. and naming reworks
            if ((Boolean) result._1()) {
                IBuiltInRuleApp app = SMTRuleApp.RULE.createApp("Isabelle " + result._2()._2().head());
                app.tryToInstantiate(mediator.getSelectedGoal());
                mediator.getSelectedGoal().apply(app);
            }

            filePaths.add(translationFile.toPath());


            try {
                Files.createDirectories(translationFile.toPath().getParent());
                Files.write(translationFile.toPath(), translation.toString().getBytes());
                LOGGER.info("Saved to: " + translationFile.toPath());
            } catch (IOException e) {
                //TODO handle exception
                throw new RuntimeException(e);
            }
            /*
            Builder<Path, Seq<Path>> builder = Seq.newBuilder();
            for (Path path : filePaths) {
                builder.addOne(path);
            }


            Seq<Path> pathSeq = builder.result();
            //TODO improve concurrency?
            Thread isabelleJEdit = new Thread(() -> Isabelle.jedit(setup, pathSeq));

            isabelleJEdit.start();*/
        } catch (IllegalFormulaException e) {
            //TODO output alert to user
            throw new RuntimeException(e);
        }
    }
}
