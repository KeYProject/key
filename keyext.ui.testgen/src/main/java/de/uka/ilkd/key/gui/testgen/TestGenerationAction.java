/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.testgen;

import java.awt.event.ActionEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;


/**
 * Action which generates test cases for all open nodes. If the proof is closed, test cases will be
 * generated for nodes on which the emptyModality rule was applied.
 *
 * @author mihai
 */
public class TestGenerationAction extends MainWindowAction implements PropertyChangeListener {
    private static final long serialVersionUID = -4911859008849602897L;

    private static final String NAME = "Generate Testcases...";
    private static final String TOOLTIP = "Generate test cases for open goals";
    private static final String TOOLTIP_EXTRA = ". Install Z3 to enable this functionality!";
    private boolean haveZ3CE = false;

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
        dlg.setLocationRelativeTo(mainWindow);
    }


    /**
     * Registers the action at some listeners to update its status in a correct fashion. This method
     * has to be invoked after the Main class has been initialised with the KeYMediator.
     */
    public void init() {
        ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings()
                .addPropertyChangeListener(this);
        checkZ3CE();

        final KeYSelectionListener selListener = new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                setEnabled(haveZ3CE && proof != null);
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }
        };
        getMediator().addKeYSelectionListener(selListener);
        // This method delegates the request only to the UserInterfaceControl which implements the
        // functionality.
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
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }

    /**
     * @return whether Z3 is installed
     */
    private boolean checkZ3CE() {
        haveZ3CE = SolverTypes.Z3_CE_SOLVER.isInstalled(false);
        if (!haveZ3CE) {
            setEnabled(false);
            setTooltip(TOOLTIP + TOOLTIP_EXTRA);
        } else if (!isEnabled()) {
            setEnabled(getMediator().getSelectedProof() != null);
            setTooltip(TOOLTIP);
        }
        return haveZ3CE;
    }

    @Override
    public void propertyChange(PropertyChangeEvent evt) {
        checkZ3CE();
    }
}
