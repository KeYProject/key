/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.gui.controller;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.*;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.translation.IllegalFormulaException;
import org.key_project.isabelletranslation.translation.IsabelleTranslator;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to translate the selected goal.
 */
@NullMarked
public class IsabelleTranslationAction extends MainWindowAction {

    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslationAction.class);

    /**
     * The {@code setName} call below operates on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here since the change is purely local,
     * suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public IsabelleTranslationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translating...");

        KeYMediator mediator = getMediator();
        Goal goal = getMediator().getSelectedGoal();
        if (goal == null) {
            throw new NullPointerException("No goal selected for translation.");
        }
        solveGoals(ImmutableList.of(goal), mediator, mainWindow);
    }

    static void solveGoals(ImmutableList<Goal> goals, KeYMediator mediator, MainWindow mainWindow) {
        IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
        Services services = mediator.getServices();
        if (services == null) {
            throw new NullPointerException("No services available for translation.");
        }
        IsabelleTranslator translator = new IsabelleTranslator(services);

        List<IsabelleProblem> translations = new ArrayList<>();
        Map<Goal, IllegalFormulaException> translationExceptions = new HashMap<>();
        for (Goal goal : goals) {
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

            Proof proof = mediator.getSelectedProof();
            if (proof == null) {
                throw new NullPointerException("No proof selected for translation.");
            }
            IsabelleLauncherProgressDialogMediator progressDialogMediator =
                new IsabelleLauncherProgressDialogMediator(proof, launcher);

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
