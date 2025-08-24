/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.GeneralSettings;

/**
 * This action is one part of the previous UndoLastStepAction: It prunes the proof tree below the
 * selected node. It now also works on closed branches if not the flag "--no-pruning-closed" is set
 * (to save memory).
 *
 * The action is enabled if any inner node selected.
 *
 * @author Pfeifer (enabled pruning in closed branches)
 */
public final class PruneProofAction extends MainWindowAction {
    /**
     * Creates a new PruneProofAction.
     *
     * @param mainWindow the MainWindow this action belongs to (needed for shortcut and icon
     *        settings)
     */
    public PruneProofAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Prune Proof");
        setSmallIcon(IconFactory.pruneLogo(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Prune the tree below the selected node.");
        enabledOnAnActiveProof();
        enabledWhenNotInAutoMode();

        Pred pruningAllowed = () -> {
            var selNode = getMediator().getSelectedNode();
            if (selNode == null)
                return false;
            final var empty = selNode.proof().getClosedSubtreeGoals(selNode).isEmpty();
            return !selNode.leaf() && (!selNode.proof().getSubtreeGoals(selNode).isEmpty()
                    || (!GeneralSettings.noPruningClosed && !empty));
        };
        setEnabledWhen(getEnabledWhen().and(pruningAllowed));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        getMediator().setBack(getMediator().getSelectedNode());
    }
}
