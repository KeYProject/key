/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;

/**
 * This action is responsible for the invocation of an SMT solver For example the toolbar button is
 * parameterized with an instance of this action
 *
 * @author ?
 * @author Alicia Appelhagen (move from MainWindow to own class)
 */
public class SMTInvokeAction extends MainWindowAction {

    private static final long serialVersionUID = -8176122007799747342L;

    protected final transient KeYMediator mediator;

    /**
     * The solver types to be run by this action.
     */
    private final transient SolverTypeCollection solverUnion;

    /**
     * Create a new SMTInvokeAction belonging to the given MainWindow. The resulting action starts
     * the given solver union.
     *
     * @param solverUnion the solvers/solver types to be started by this action
     * @param mainWindow the main window this action belongs to
     */
    public SMTInvokeAction(SolverTypeCollection solverUnion, MainWindow mainWindow) {
        super(mainWindow);
        this.mediator = mainWindow.getMediator();
        this.solverUnion = solverUnion;
        if (solverUnion != SolverTypeCollection.EMPTY_COLLECTION) {
            putValue(SHORT_DESCRIPTION, "Invokes " + solverUnion.toString());
        }
    }

    public SolverTypeCollection getSolverUnion() {
        return solverUnion;
    }

    @Override
    public boolean isEnabled() {
        return super.isEnabled() && solverUnion != SolverTypeCollection.EMPTY_COLLECTION
                && mediator != null && mediator.getSelectedProof() != null
                && !mediator.getSelectedProof().closed();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (!mediator.ensureProofLoaded() || solverUnion == SolverTypeCollection.EMPTY_COLLECTION) {
            mainWindow.popupWarning("No proof loaded or no solvers selected.", "Oops...");
            return;
        }
        final Proof proof = mediator.getSelectedProof();

        Thread thread = new Thread(() -> {

            DefaultSMTSettings settings =
                new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                    proof.getSettings().getNewSMTSettings(), proof);
            SolverLauncher launcher = new SolverLauncher(settings);
            launcher.addListener(new SolverListener(settings, proof));
            launcher.launch(solverUnion.getTypes(), SMTProblem.createSMTProblems(proof),
                proof.getServices());

        }, "SMTRunner");
        thread.start();

    }

    @Override
    public String toString() {
        return solverUnion.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof SMTInvokeAction)) {
            return false;
        }
        return this.solverUnion.equals(((SMTInvokeAction) obj).solverUnion);
    }

    @Override
    public int hashCode() {
        return solverUnion.hashCode() * 7;
    }

}
