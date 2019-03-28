package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.HeatmapOptionsDialog;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ext.KeYExtConst;
import de.uka.ilkd.key.proof.Proof;

import java.awt.event.ActionEvent;

/**
 * Action for invoking the heatmap options dialog.
 *
 * @author jschiffl
 */
public class HeatmapSettingsAction extends MainWindowAction {
    private HeatmapOptionsDialog dialog;

    /**
     * constructor
     *
     * @param mainWindow the main window of the options dialog
     */
    public HeatmapSettingsAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Heatmap Options");
        putValue(KeYExtConst.PATH, "Heatmap");
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
