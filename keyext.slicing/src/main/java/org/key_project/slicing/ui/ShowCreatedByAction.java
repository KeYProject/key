/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Node;

/**
 * Context menu action to select the proof step that created a formula.
 *
 * @author Arne Keller
 */
public class ShowCreatedByAction extends MainWindowAction {

    private static final long serialVersionUID = 1475202264543002419L;

    /**
     * The node to switch to.
     */
    private final transient Node node;

    /**
     * Construct a new action.
     *
     * @param mw main window
     * @param node node to switch to
     */
    public ShowCreatedByAction(MainWindow mw, Node node) {
        super(mw);
        setName(String.format(
            "Show proof step that created this formula (switches to proof step %d)",
            node.serialNr()));
        this.node = node;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        getMediator().getSelectionModel().setSelectedNode(node);
    }
}
