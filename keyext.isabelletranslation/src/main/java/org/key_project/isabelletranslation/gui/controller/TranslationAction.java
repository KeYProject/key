/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.gui.controller;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.translation.IllegalFormulaException;
import org.key_project.isabelletranslation.translation.IsabelleTranslator;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to translate the selected goal.
 */
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
        IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();

        IsabelleProblem translation;
        try {
            translation = translator.translateProblem(mediator.getSelectedGoal());
        } catch (IllegalFormulaException e) {
            LOGGER.error("Failed to generate translation", e);
            return;
        }

        List<IsabelleProblem> list = new ArrayList<>();

        list.add(translation);

        Thread thread = new Thread(() -> {
            IsabelleLauncher launcher;
            try {
                launcher = new IsabelleLauncher(settings);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }

            IsabelleLauncherProgressDialogMediator progressDialogMediator =
                new IsabelleLauncherProgressDialogMediator(
                    mediator.getSelectedProof(), launcher);

            launcher.addListener(progressDialogMediator);
            try {
                launcher.launch(list, settings.getTimeout(), 1);
            } catch (IOException e) {
                progressDialogMediator.discardEvent();
            }
        }, "IsabelleLauncherThread");
        thread.start();
    }
}
