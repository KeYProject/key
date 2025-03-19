/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

public class HeatmapToggleAction extends MainWindowAction {
    private static final long serialVersionUID = 1L;

    public static final Icon ICON_SELECTED = IconFactory.HEATMAP_DEACTIVATE.get();
    public static final Icon ICON_NOT_SELECTED = IconFactory.HEATMAP_ACTIVATE.get();

    public HeatmapToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Toggle Heatmap");
        setMenuPath("View.Heatmap");
        setEnabled(getMediator().getSelectedProof() != null);
        putValue(Action.LONG_DESCRIPTION, "Enable or disable age heatmaps in the sequent view.");

        setIcon();
        addPropertyChangeListener(evt -> {
            if (evt.getPropertyName().equals(SELECTED_KEY)) {
                setIcon();
            }
        });

        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        setSelected(vs.isShowHeatmap());
        final PropertyChangeListener setListener = e -> setSelected(vs.isShowHeatmap());
        vs.addPropertyChangeListener(setListener);

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

    private void setIcon() {
        setIcon(isSelected() ? ICON_SELECTED : ICON_NOT_SELECTED);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        vs.setHeatmapOptions(!vs.isShowHeatmap(), vs.isHeatmapSF(), vs.isHeatmapNewest(),
            vs.getMaxAgeForHeatmap());
    }
}
