/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;
import java.io.IOException;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to add a proof to the proof caching database.
 *
 * @author Arne Keller
 * @see CachingDatabase
 */
public class AddToDatabaseAction extends KeyAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(AddToDatabaseAction.class);

    /**
     * Proof to add.
     */
    private final Proof proof;

    /**
     * Create a new action.
     *
     * @param proof proof to add
     */
    AddToDatabaseAction(Proof proof) {
        this.proof = proof;

        setName("Add to proof caching database");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            CachingDatabase.addProof(proof);
        } catch (IOException ex) {
            LOGGER.warn("failed to add proof ", ex);
            IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
        }
    }
}