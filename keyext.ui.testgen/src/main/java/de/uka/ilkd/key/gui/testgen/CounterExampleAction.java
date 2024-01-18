/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.testgen;

import java.awt.event.ActionEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.testgen.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.testgen.smt.counterexample.AbstractCounterExampleGenerator;
import de.uka.ilkd.key.testgen.smt.counterexample.AbstractSideProofCounterExampleGenerator;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class CounterExampleAction extends MainWindowAction implements PropertyChangeListener {
    private static final long serialVersionUID = -1931682474791981751L;
    private static final Logger LOGGER = LoggerFactory.getLogger(CounterExampleAction.class);

    private static final String NAME = "Search for Counterexample";
    private static final String TOOLTIP = "Search for a counterexample for the selected goal";
    private static final String TOOLTIP_EXTRA = ". Install Z3 to enable this functionality!";
    private boolean haveZ3CE = false;

    public CounterExampleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOLTIP);
        Icon icon = IconFactory.counterExample(MainWindow.TOOLBAR_ICON_SIZE);
        putValue(SMALL_ICON, icon);
        setMenuPath("Proof");
        init();
        lookupAcceleratorKey();
    }

    /**
     * Registers the action at some listeners to update its status in a correct fashion. This method
     * has to be invoked after the Main class has been initialized with the KeYMediator.
     * <p>
     * <b>This class provides only the user interface and no counter example generation logic which
     * is implemented by the {@link AbstractCounterExampleGenerator}</b>.
     */
    public void init() {
        ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings()
                .addPropertyChangeListener(this);
        checkZ3CE();

        final KeYSelectionListener selListener = new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                if (proof == null) {
                    // no proof loaded
                    setEnabled(false);
                } else {
                    final Node selNode = getMediator().getSelectedNode();
                    // Can be applied only to root nodes
                    setEnabled(haveZ3CE && selNode.childrenCount() == 0 && !selNode.isClosed());
                }
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

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            // Get required information
            final Goal goal = getMediator().getSelectedGoal();
            if (goal != null) {
                final Node node = goal.node();
                // Start SwingWorker (CEWorker) in which counter example search is performed.
                final CEWorker worker = new CEWorker(node.proof(), node.sequent());
                worker.start();
            }
        } catch (Exception exc) {
            LOGGER.error("", exc);
            IssueDialog.showExceptionDialog(mainWindow, exc);
        }
    }

    @Override
    public void propertyChange(PropertyChangeEvent evt) {
        checkZ3CE();
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
            Node selNode = getMediator().getSelectedNode();
            setEnabled(selNode != null && selNode.childrenCount() == 0 && !selNode.isClosed());
            setTooltip(TOOLTIP);
        }
        return haveZ3CE;
    }

    /**
     * Performs the {@link SemanticsBlastingMacro} in a side proof hidden to the user and shows the
     * result with help of the {@link SolverListener}.
     */
    public static class NoMainWindowCounterExampleGenerator
            extends AbstractSideProofCounterExampleGenerator {
        /**
         * {@inheritDoc}
         */
        @Override
        protected SolverLauncherListener createSolverListener(DefaultSMTSettings settings,
                Proof proof) {
            return new SolverListener(settings, proof);
        }
    }

    /**
     * <strong>The worker must be started using method {@link CEWorker#start()} and not
     * via the standard {@link #execute()}</strong>.
     */
    private class CEWorker extends SwingWorker<Void, Void> implements InterruptListener {
        private final Proof oldProof;
        private final Sequent oldSequent;

        public CEWorker(Proof oldProof, Sequent oldSequent) {
            this.oldProof = oldProof;
            this.oldSequent = oldSequent;
        }

        public void start() {
            getMediator().initiateAutoMode(oldProof, true, false);
            getMediator().addInterruptedListener(this);
            execute();
        }

        @Override
        protected Void doInBackground() throws Exception {
            final NoMainWindowCounterExampleGenerator generator =
                new NoMainWindowCounterExampleGenerator();
            generator.searchCounterExample(getMediator().getUI(), oldProof, oldSequent);
            return null;
        }

        @Override
        public void interruptionPerformed() {
            cancel(true);
        }

        @Override
        protected void done() {
            getMediator().finishAutoMode(oldProof, true, true, null);
            getMediator().removeInterruptedListener(this);
        }

    }
}
