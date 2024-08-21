package key.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTRuleApp;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.unruh.isabelle.control.Isabelle;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
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
        LOGGER.info("Translating...");

        generateTranslation();
    }


    private void generateTranslation() {
        KeYMediator mediator = getMediator();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());

        IsabelleProblem translation;
        try {
            translation = translator.translateProblem(mediator.getSelectedGoal());
        } catch (IllegalFormulaException e) {
            LOGGER.error("Failed to generate translation", e);
            return;
        }

        writeTranslationFiles(translation);

        List<IsabelleProblem> list = new ArrayList<>();

        list.add(translation);

        SledgehammerResult result = null;
            Thread thread = new Thread(() -> {

                IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
                IsabelleLauncher launcher;
                try {
                    launcher = new IsabelleLauncher(IsabelleTranslationSettings.getInstance());
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }

                launcher.addListener(new IsabelleSimpleSolverListener(settings));
                try {
                    launcher.try0ThenSledgehammerAllPooled(list, 30, 1);
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }

            }, "IsabelleControlThread");
            thread.start();
        result = translation.getResult();
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
