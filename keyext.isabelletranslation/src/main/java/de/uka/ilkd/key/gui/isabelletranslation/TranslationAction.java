package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.*;
import de.unruh.isabelle.pure.*;
import de.unruh.isabelle.pure.Implicits;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.Tuple2;
import scala.collection.immutable.Seq;
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

    private void generateTranslation() {
        KeYMediator mediator = getMediator();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());
        try {
            //TODO let user choose where to save file?
            File translationFile = new File(System.getProperty("user.home") + "/.key/IsabelleTranslations/Translation.thy");
            StringBuilder translation = translator.translateProblem(mediator.getSelectedGoal().sequent());

            //TODO find Isabelle path
            Isabelle.Setup setup = JIsabelle.setup(Path.of("C:\\Users\\nilsb\\Desktop\\Isabelle2023"));
            Isabelle isabelle = new Isabelle(setup);
            //TODO automatically run try/sledgehammer instead of opening Isabelle
            List<Path> filePaths = new ArrayList<>();


            MLFunction2<String, Position, TheoryHeader> getHeader =  MLValue.compileFunction("fn (text,pos) => Thy_Header.read pos text", isabelle, new StringConverter(), Implicits.positionConverter(), Implicits.theoryHeaderConverter());
            TheoryHeader theoryHeader = getHeader.apply(translation.toString(), Position.none(isabelle), isabelle, new StringConverter(), Implicits.positionConverter()).retrieveNow(Implicits.theoryHeaderConverter(), isabelle);
            MLFunction3<Path, TheoryHeader, scala.collection.immutable.List<Theory>, Theory> begin_theory = MLValue.compileFunction("fn (path, header, parents) => Resources.begin_theory path header parents", isabelle, Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()), Implicits.theoryConverter());
            Theory thy0 = Theory.apply(translationFile.toPath(), isabelle);
            MLFunction0<ToplevelState> init_toplevel = MLValue.compileFunction0("Toplevel.init_toplevel", isabelle, Implicits.toplevelStateConverter());
            ToplevelState toplevel = init_toplevel.apply(isabelle).retrieveNow(Implicits.toplevelStateConverter(), isabelle);

            MLFunction2<Theory, String, scala.collection.immutable.List<Tuple2<Transition, String>>> parse_text = MLValue.compileFunction(
                    """
                      fn (thy, text) => let
                      |  val transitions = Outer_Syntax.parse_text thy (K thy) Position.start text
                      |  fun addtext symbols [tr] =
                      |        [(tr, implode symbols)]
                      |    | addtext _ [] = []
                      |    | addtext symbols (tr::nextTr::trs) = let
                      |        val (this,rest) = Library.chop (Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of nextTr) |> Option.valOf) symbols
                      |        in (tr, implode this) :: addtext rest (nextTr::trs) end
                      |  in addtext (Symbol.explode text) transitions end
                      """, isabelle, Implicits.theoryConverter(), new StringConverter());

            val command_exception = compileFunction[Boolean, Transition.T, ToplevelState, ToplevelState](
                    "fn (int, tr, st) => Toplevel.command_exception int tr st")

            for ((transition, text) <- parse_text(thy0, theorySource.text).force.retrieveNow) {
                println(s"""Transition: "${text.strip}"""")
                toplevel = command_exception(true, transition, toplevel).retrieveNow.force
            }

            //    val finalThy = toplevel_end_theory(toplevel).retrieveNow.force

            val thy_for_sledgehammer = thy0
            val Sledgehammer: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer")
            val Sledgehammer_Commands: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Commands")
            val Sledgehammer_Prover: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Prover")

            val normal_with_Sledgehammer: MLFunction4[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))] =
            compileFunction[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))](
                    s""" fn (state, thy, adds, dels) =>
           |    let
           |       val override = {add=[],del=[],only=false};
           |       fun go_run (state, thy) =
           |          let
           |             val p_state = Toplevel.proof_of state;
           |             val ctxt = Proof.context_of p_state;
           |             val params = ${Sledgehammer_Commands}.default_params thy
           |                [("provers", "e"),("timeout","30"),("verbose","true")];
           |             val results = ${Sledgehammer}.run_sledgehammer params ${Sledgehammer_Prover}.Normal NONE 1 override p_state;
           |             val (result, (outcome, step)) = results;
           |           in
           |             (result, (${Sledgehammer}.short_string_of_sledgehammer_outcome outcome, [YXML.content_of step]))
           |           end;
           |    in
           |      Timeout.apply (Time.fromSeconds 35) go_run (state, thy) end
           |""".stripMargin
      )
            filePaths.add(translationFile.toPath());


            try {
                Files.createDirectories(translationFile.toPath().getParent());
                Files.write(translationFile.toPath(), translation.toString().getBytes());
                LOGGER.info("Saved to: " + translationFile.toPath());
            } catch (IOException e) {
                //TODO handle exception
                throw new RuntimeException(e);
            }

            Builder<Path, Seq<Path>> builder = Seq.newBuilder();
            for (Path path : filePaths) {
                builder.addOne(path);
            }


            Seq<Path> pathSeq = builder.result();
            //TODO improve concurrency?
            Thread isabelleJEdit = new Thread(() -> Isabelle.jedit(setup, pathSeq));

            isabelleJEdit.start();
        } catch (IllegalFormulaException e) {
            //TODO output alert to user
            throw new RuntimeException(e);
        }
    }
}
