package org.key_project.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTRuleApp;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

public class TranslateAllAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(TranslateAllAction.class);

    public TranslateAllAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate all goals to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translating...");

        generateTranslation();
    }


    private void generateTranslation() {
        KeYMediator mediator = getMediator();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());

        List<IsabelleProblem> translations = new ArrayList<>();
        try {
            for (Goal goal : mediator.getSelectedProof().openGoals()) {
                translations.add(translator.translateProblem(goal));
            }
        } catch (IllegalFormulaException e) {
            LOGGER.error("Failed to generate translation", e);
            return;
        }

        writeTranslationFiles(translations.get(0));

        IsabelleResult result = null;
        Thread thread = new Thread(() -> {

            IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
            IsabelleLauncher launcher;
            try {
                launcher = new IsabelleLauncher(IsabelleTranslationSettings.getInstance());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }

            launcher.addListener(new IsabelleLauncherProgressDialogMediator(settings, mediator.getSelectedProof()));
            try {
                launcher.try0ThenSledgehammerAllPooled(translations, 30, 1);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }

        }, "IsabelleControlThread");
        thread.start();
        //result = translation.getResult();
        //SledgehammerResult result = translation.sledgehammer(30);

        //TODO needs its own action to enable undo, etc. and naming reworks
        if (result != null && result.isSuccessful()) {
            IBuiltInRuleApp app = SMTRuleApp.RULE.createApp("Isabelle " + result.getSuccessfulTactic());
            app.tryToInstantiate(mediator.getSelectedGoal());
            mediator.getSelectedGoal().apply(app);
        }
    }

    protected static void writeTranslationFiles(IsabelleProblem translation) {
        File translationFile = new File(IsabelleTranslationSettings.getInstance().getTranslationPath() + "/Translation.thy");
        File translationPreambleFile = new File(IsabelleTranslationSettings.getInstance().getTranslationPath() + "/TranslationPreamble.thy");
        try {
            Files.createDirectories(translationFile.toPath().getParent());
            Files.write(translationPreambleFile.toPath(), translation.getPreamble().getBytes());
            Files.write(translationFile.toPath(), translation.getSequentTranslation().getBytes());
            LOGGER.info("Saved to: " + translationFile.toPath() + " and " + translationPreambleFile.toPath());
        } catch (IOException e) {
            LOGGER.error("Failed to save translation", e);
            return;
        }
    }
}
