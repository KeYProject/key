package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.Icon;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

public class HeatmapToolbarAction extends MainWindowAction {

    private static final Icon HEATMAP_ON_ICON = IconFactory.heatmapOnIcon(MainWindow.TOOLBAR_ICON_SIZE);
    private static final Icon HEATMAP_OFF_ICON = IconFactory.heatmapOffIcon(MainWindow.TOOLBAR_ICON_SIZE);

    /**
     * version id
     */
    private static final long serialVersionUID = 5551666060738982540L;

    private static final ViewSettings VS = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();

    public HeatmapToolbarAction(MainWindow main) {
        super(main);
        putValue(NAME, "Enable/Disable Age Heatmaps");
        setIcon();
        putValue(SHORT_DESCRIPTION,
                "Enable or disable age heatmaps in the sequent view.");
        setEnabled(false);
        initListener();
    }

    public void initListener() {
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
        VS.setHeatmapOptions(!VS.isShowHeatmap(), VS.isHeatmapSF(), VS.isHeatmapNewest(), VS.getMaxAgeForHeatmap());
        setIcon();
    }

    private void setIcon() {
        if (VS.isShowHeatmap()) {
            putValue(SMALL_ICON, HEATMAP_ON_ICON);
        } else {
            putValue(SMALL_ICON, HEATMAP_OFF_ICON);
        }
    }

}
