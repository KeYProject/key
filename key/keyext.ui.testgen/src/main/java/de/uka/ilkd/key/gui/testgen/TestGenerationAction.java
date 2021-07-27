package de.uka.ilkd.key.gui.testgen;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;

import javax.swing.*;
import java.awt.event.ActionEvent;


/**
 * Action which generates test cases for all open nodes. If the proof is closed,
 * test cases will be generated for nodes on which the emptyModality rule was
 * applied.
 *
 * @author mihai
 */
public class TestGenerationAction extends MainWindowAction {
    private static final long serialVersionUID = -4911859008849602897L;

    private static final String NAME = "Generate Testcases";
    private static final String TOOLTIP = "Generate test cases for open goals";

    public TestGenerationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(TestGenerationAction.NAME);
        setTooltip(TestGenerationAction.TOOLTIP);
        Icon icon = IconFactory.testGeneration(MainWindow.TOOLBAR_ICON_SIZE);
        putValue(SMALL_ICON, icon);
        setMenuPath("Proof");
        init();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        TGInfoDialog dlg = new TGInfoDialog(mainWindow);
        dlg.setVisible(true);
    }


    /**
     * Registers the action at some listeners to update its status in a correct
     * fashion. This method has to be invoked after the Main class has been
     * initialised with the KeYMediator.
     */
    public void init() {
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
        // This method delegates the request only to the UserInterfaceControl which implements the functionality.
        // No functionality is allowed in this method body!
        getMediator().getUI().getProofControl().addAutoModeListener(new AutoModeListener() {
            @Override
            public void autoModeStarted(ProofEvent e) {
                getMediator().removeKeYSelectionListener(selListener);
                setEnabled(false);
            }

            @Override
            public void autoModeStopped(ProofEvent e) {
                getMediator().addKeYSelectionListener(selListener);
            }
        });
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator()
                .getSelectionModel()));
    }
}
