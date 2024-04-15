package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTRuleApp;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

public class TranslationAction extends MainWindowAction {

    private static final Logger LOGGER = LoggerFactory.getLogger(TranslationAction.class);

    public TranslationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translating...");

        generateTranslation();
    }


    private void generateTranslation() {
        KeYMediator mediator = getMediator();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());

        File translationFile = new File(IsabelleTranslationSettings.getInstance().getTranslationPath() + "\\Translation.thy");
        File translationPreambleFile = new File(IsabelleTranslationSettings.getInstance().getTranslationPath() + "\\TranslationPreamble.thy");
        IsabelleProblem translation;
        try {
            translation = translator.translateProblem(mediator.getSelectedGoal());
        } catch (IllegalFormulaException e) {
            LOGGER.error("Failed to generate translation", e);
            return;
        }

        try {
            Files.createDirectories(translationFile.toPath().getParent());
            Files.write(translationPreambleFile.toPath(), translation.getPreamble().getBytes());
            Files.write(translationFile.toPath(), translation.getSequentTranslation().getBytes());
            LOGGER.info("Saved to: " + translationFile.toPath() + " and " + translationPreambleFile.toPath());
        } catch (IOException e) {
            LOGGER.error("Failed to save translation", e);
            return;
        }

        SledgehammerResult result = translation.sledgehammer();

        //TODO needs its own action to enable undo, etc. and naming reworks
        if (result != null && result.isSuccessful()) {
            IBuiltInRuleApp app = SMTRuleApp.RULE.createApp("Isabelle " + result.getSuccessfulTactic());
            app.tryToInstantiate(mediator.getSelectedGoal());
            mediator.getSelectedGoal().apply(app);
        }



            /*
            List<Path> filePaths = new ArrayList<>();
            filePaths.add(translationFile.toPath());

            Builder<Path, Seq<Path>> builder = Seq.newBuilder();
            for (Path path : filePaths) {
                builder.addOne(path);
            }


            Seq<Path> pathSeq = builder.result();
            //TODO improve concurrency?
            Thread isabelleJEdit = new Thread(() -> Isabelle.jedit(setup, pathSeq));

            isabelleJEdit.start();*/
    }
}
