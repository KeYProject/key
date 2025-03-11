/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
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
     *
     */
    private static final long serialVersionUID = 9133317783386913373L;

    /**
     * Creates a new PruneProofAction.
     *
     * @param mainWindow the MainWindow this action belongs to (needed for shortcut and icon
     *        settings)
     */
    public PruneProofAction(MainWindow mainWindow) {
        super(mainWindow);
        init();
        putValue(NAME, "Prune Proof");
        putValue(SMALL_ICON, IconFactory.pruneLogo(MainWindow.TOOLBAR_ICON_SIZE));
        putValue(SHORT_DESCRIPTION, "Prune the tree below the selected node.");
    }

    /**
     * Registers the action at some listeners to update its status in a correct fashion. This method
     * has to be invoked after the Main class has been initialized with the KeYMediator.
     */
    public void init() {
        final KeYSelectionListener selListener = new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                boolean enabled = false;
                if (proof != null) {
                    final Node selNode = getMediator().getSelectedNode();

                    if (selNode != null) {
                        /*
                         * disable pruning for leaves and disable it for closed subtrees if the
                         * command line option "--no-pruning-closed" is set (saves memory)
                         */
                        if (!selNode.leaf() && (proof.getSubtreeGoals(selNode).size() > 0
                                || (!GeneralSettings.noPruningClosed
                                        && proof.getClosedSubtreeGoals(selNode).size() > 0))) {

                            enabled = true;
                        }
                    }
                }
                setEnabled(enabled);
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }
        };

        getMediator().addKeYSelectionListener(selListener);

        /*
         * This method delegates the request only to the UserInterfaceControl which implements the
         * functionality. No functionality is allowed in this method body!
         */
        getMediator().getUI().getProofControl().addAutoModeListener(new AutoModeListener() {
            @Override
            public void autoModeStarted(ProofEvent e) {
                getMediator().removeKeYSelectionListener(selListener);
                setEnabled(false);
            }

            @Override
            public void autoModeStopped(ProofEvent e) {
                getMediator().addKeYSelectionListener(selListener);
                selListener.selectedNodeChanged(null);
            }
        });
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        getMediator().setBack(getMediator().getSelectedNode());
    }
}
