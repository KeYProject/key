/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.gui.controller;

import java.awt.event.ActionEvent;
import java.util.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to translate all open goals.
 */
@NullMarked
public class IsabelleTranslateAllAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslateAllAction.class);

    /**
     * The {@code setName} call below operates on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here since the change is purely local,
     * suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public IsabelleTranslateAllAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate all goals to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translating...");

        KeYMediator mediator = getMediator();
        Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            throw new NullPointerException("No proof selected for translation.");
        }
        IsabelleTranslationAction.solveGoals(proof.openGoals(), mediator, mainWindow);
    }
}
