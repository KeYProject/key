/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.gui.controller;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.*;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.translation.IllegalFormulaException;
import org.key_project.isabelletranslation.translation.IsabelleTranslator;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to translate the selected goal.
 */
public class IsabelleTranslationAction extends MainWindowAction {

    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslationAction.class);

    public IsabelleTranslationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translating...");

        KeYMediator mediator = getMediator();
        solveGoals(ImmutableList.of(getMediator().getSelectedGoal()), mediator, mainWindow);
    }

    static void solveGoals(ImmutableList<Goal> goals, KeYMediator mediator, MainWindow mainWindow) {
        IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());

        List<IsabelleProblem> translations = new ArrayList<>();
        Map<Goal, IllegalFormulaException> translationExceptions = new HashMap<>();
        for (Goal goal : Objects.requireNonNull(goals)) {
            try {
                translations.add(translator.translateProblem(goal));
            } catch (IllegalFormulaException e) {
                translationExceptions.put(goal, e);
                // Add problem without translation
                translations.add(new IsabelleProblem(goal, translationExceptions.get(goal)));
            }
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
                // Thrown when Isabelle was not found or translation files could not be written
                progressDialogMediator.discardEvent();
                JOptionPane.showMessageDialog(mainWindow, e.getMessage(), "Launch failed!",
                    JOptionPane.ERROR_MESSAGE);
            }
        }, "IsabelleLauncherThread");
        thread.start();
    }
}
