package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
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
            Isabelle.Setup setup = JIsabelle.setup(Path.of("C:\\Users\\Nils\\Documents\\Isabelle2023"));

            //TODO automatically run try/sledgehammer instead of opening Isabelle
            //Isabelle isabelle = new Isabelle(setup);
            //Context context = Context.apply("Main", isabelle);
            //Term translationTerm = Term.apply(context, translation.toString(), Symbols.globalInstance(), isabelle);

            //isabelle.destroy();

            List<Path> filePaths = new ArrayList<>();
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
            Thread isabelleJEdit = new Thread() {
                public void run() {

                    Isabelle.jedit(setup, pathSeq);
                }
            };

            isabelleJEdit.start();
        } catch (IllegalFormulaException e) {
            //TODO output alert to user
            throw new RuntimeException(e);
        }
    }
}
