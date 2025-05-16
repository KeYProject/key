/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.gui.controller;

import java.awt.event.ActionEvent;
import java.util.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to translate all open goals.
 */
public class IsabelleTranslateAllAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslateAllAction.class);

    public IsabelleTranslateAllAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate all goals to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translating...");

        KeYMediator mediator = getMediator();
        IsabelleTranslationAction.solveGoals(
            Objects.requireNonNull(mediator.getSelectedProof()).openGoals(), mediator, mainWindow);
    }
}
