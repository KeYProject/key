/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.HeatmapOptionsDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;

/**
 * Action for invoking the heatmap options dialog.
 *
 * @author jschiffl
 */
public class HeatmapSettingsAction extends MainWindowAction {
    private static final long serialVersionUID = -6165100588113899099L;

    private HeatmapOptionsDialog dialog;

    /**
     * constructor
     *
     * @param mainWindow the main window of the options dialog
     */
    public HeatmapSettingsAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Heatmap Options");
        setMenuPath("View.Heatmap");
        setEnabled(getMediator().getSelectedProof() != null);
        setIcon(IconFactory.selectDecProcArrow(MainWindow.TOOLBAR_ICON_SIZE));

        final KeYSelectionListener selListener = new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                setEnabled(proof != null);
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }
        };
        getMediator().addKeYSelectionListener(selListener);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        getDialog().setVisible(true);
    }

    private HeatmapOptionsDialog getDialog() {
        if (dialog == null) {
            dialog = new HeatmapOptionsDialog();
        }
        return dialog;
    }
}
