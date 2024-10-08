package org.key_project.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTRuleApp;
import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.automation.IsabelleResult;
import org.key_project.isabelletranslation.automation.IsabelleSolverListener;
import org.key_project.isabelletranslation.translation.IllegalFormulaException;
import org.key_project.isabelletranslation.translation.IsabelleTranslator;
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
        IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
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

        translations.get(0).writeTranslationFiles(settings);

        Thread thread = new Thread(() -> {
            IsabelleLauncher launcher;
            try {
                launcher = new IsabelleLauncher(IsabelleTranslationSettings.getInstance());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }

            launcher.addListener(new IsabelleSolverListener.IsabelleLauncherProgressDialogMediator(mediator.getSelectedProof()));
            try {
                launcher.try0ThenSledgehammerAllPooled(translations, settings.getTimeout(), 1);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }

        }, "IsabelleControlThread");
        thread.start();
    }
}
