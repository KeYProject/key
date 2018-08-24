package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.EventObject;

import javax.swing.JToggleButton;
import javax.swing.Timer;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.HeatmapOptionsDialog;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;
import de.uka.ilkd.key.settings.ViewSettings;


/**
 * An action that enables toggling age heatmaps from the toolbar.
 * @author jschiffl
 */
public class HeatmapToolbarAction extends MainWindowAction implements MouseListener {

    /**
     * version id
     */
    private static final long serialVersionUID = 5551666060738982540L;

    /** view settings */
    private static final ViewSettings VS =
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();

    /** Timer for menu */
    private static Timer time;

    /** The Button associated with this action */
    JToggleButton toggleHeatmapButton;

    /** initialisation
     * @param main the main window
     * @param toggleHeatmapButton */
    public HeatmapToolbarAction(MainWindow main, JToggleButton toggleHeatmapButton) {
        super(main);
        initTimer();
        initListener();
        this.toggleHeatmapButton = toggleHeatmapButton;
        toggleHeatmapButton.setEnabled(getMediator().getSelectedProof() != null);
        toggleHeatmapButton.setSelected(VS.isShowHeatmap());
        toggleHeatmapButton.addMouseListener(this);
    }

    private void initTimer() {
        time = new Timer(1000, new HeatmapSettingsAction(mainWindow));
    }

    /** initialisation of the listener */
    private void initListener() {
        final SettingsListener setListener = new SettingsListener() {

            @Override
            public void settingsChanged(EventObject e) {
                toggleHeatmapButton.setSelected(VS.isShowHeatmap());
            }
        };
        VS.addSettingsListener(setListener);

        final KeYSelectionListener selListener = new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                toggleHeatmapButton.setEnabled(proof != null);
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
        VS.setHeatmapOptions(!VS.isShowHeatmap(), VS.isHeatmapSF(),
            VS.isHeatmapNewest(), VS.getMaxAgeForHeatmap());
    }


    @Override
    public void mousePressed(MouseEvent e) {
        time.start();
    }

    @Override
    public void mouseReleased(MouseEvent e) {
        time.stop();
    }

    @Override
    public void mouseExited(MouseEvent e) {
        if (time.isRunning()) {
            time.stop();
        }
    }

    @Override
    public void mouseClicked(MouseEvent e) {}

    @Override
    public void mouseEntered(MouseEvent e) {}


}
