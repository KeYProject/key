/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.gui.controller;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.PositionedIssueString;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.translation.IllegalFormulaException;
import org.key_project.isabelletranslation.translation.IsabelleTranslator;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to translate all open goals.
 */
public class TranslateAllAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(TranslateAllAction.class);

    public TranslateAllAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate all goals to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translating...");

        solveOpenGoals();
    }


    private void solveOpenGoals() {
        KeYMediator mediator = getMediator();
        IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());

        List<IsabelleProblem> translations = new ArrayList<>();
        Map<Goal, IllegalFormulaException> translationExceptions = new HashMap<>();
        List<Goal> untranslatableGoals = new ArrayList<>();
        for (Goal goal : Objects.requireNonNull(mediator.getSelectedProof()).openGoals()) {
            try {
                translations.add(translator.translateProblem(goal));
            } catch (IllegalFormulaException e) {
                translationExceptions.put(goal, e);
                //Add problem without translation
                untranslatableGoals.add(goal);
            }
        }
        if (!translationExceptions.isEmpty()) {
            Set<PositionedIssueString> issueStrings = new HashSet<>();
            for (Goal goal : translationExceptions.keySet()) {
                String issueStringBuilder = "Translation failed for" +
                        "Goal " + goal.node().serialNr() + ":  " +
                        translationExceptions.get(goal).getMessage();
                issueStrings.add(new PositionedIssueString(issueStringBuilder));
            }
            IssueDialog issueDialog =
                    new IssueDialog(mainWindow, "Translations failed!", issueStrings, translations.isEmpty());
            issueDialog.setVisible(true);

            if (translations.isEmpty()) {
                return;
            }
            untranslatableGoals.forEach(goal -> translations.add(new IsabelleProblem(goal, translationExceptions.get(goal))));
        }

        Thread thread = new Thread(() -> {
            IsabelleLauncher launcher = new IsabelleLauncher(settings);

            IsabelleLauncherProgressDialogMediator progressDialogMediator =
                new IsabelleLauncherProgressDialogMediator(
                    mediator.getSelectedProof(), launcher);

            launcher.addListener(progressDialogMediator);
            try {
                launcher.launch(translations, settings.getTimeout(), 1);
            } catch (IOException e) {
                progressDialogMediator.discardEvent();
                PositionedIssueString issueString = new PositionedIssueString(
                    "Failed to launch Isabelle solvers: " + e.getMessage());
                IssueDialog issueDialog =
                    new IssueDialog(mainWindow, "Launch failed!", Set.of(issueString), true);
                issueDialog.setVisible(true);
            }
        }, "IsabelleLauncherThread");
        thread.start();
    }
}
