package de.uka.ilkd.key.gui.ext.exploration;

import java.awt.event.ActionEvent;

import javax.swing.Action;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.ext.KeYExtConst;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;

/**
 * Action to toggle {@link TermLabelSettings#getUseOriginLabels()}.
 *
 * @author lanzinger
 */
public class ToggleOriginLabelsAction extends MainWindowAction {

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleOriginLabelsAction(MainWindow mainWindow) {
        super(mainWindow);

        final TermLabelSettings settings;
        if (getMediator().getSelectedProof() != null) {
            settings = getMediator().getSelectedProof().getSettings().getTermLabelSettings();
        } else {
            settings = ProofSettings.DEFAULT_SETTINGS.getTermLabelSettings();
        }

        setName("Toggle Origin Labels");
        setIcon(IconFactory.originIcon(MainWindow.TOOLBAR_ICON_SIZE));
        setEnabled(getMediator().getSelectedProof() != null);
        setSelected(settings.getUseOriginLabels());

        settings.addSettingsListener(event -> setSelected(settings.getUseOriginLabels()));
        getMediator().addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                setEnabled(getMediator().getSelectedProof() != null);
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                setEnabled(getMediator().getSelectedProof() != null);
            }
        });

        putValue(KeYExtConst.PATH, "Origin Term Labels");
        putValue(Action.LONG_DESCRIPTION, "Toggle origin labels.");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Proof proof = mainWindow.getMediator().getSelectedProof();

        if (proof != null) {
            TermLabelSettings settings = proof.getSettings().getTermLabelSettings();
            settings.setUseOriginLabels(!settings.getUseOriginLabels());

            if (settings.getUseOriginLabels()) {
                JOptionPane.showMessageDialog(
                        mainWindow,
                        "This setting will only take effect when the proof is reloaded.",
                        "Origin",
                        JOptionPane.INFORMATION_MESSAGE);
            } else {
                JOptionPane.showMessageDialog(
                        mainWindow,
                        "This setting will be in effect for all following proof steps.",
                        "Origin",
                        JOptionPane.INFORMATION_MESSAGE);
            }
        }
    }
}
