/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This action is responsible for the invocation of an SMT solver For example the toolbar button is
 * parameterized with an instance of this action
 *
 * @author ?
 * @author Alicia Appelhagen (move from MainWindow to own class)
 */
@NullMarked
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
    /**
     * The action-configuration setter is called on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
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
        KeYMediator m = mediator;
        Proof proof = m != null ? m.getSelectedProof() : null;
        return super.isEnabled() && solverUnion != SolverTypeCollection.EMPTY_COLLECTION
                && m != null && proof != null
                && !proof.closed();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (!mediator.ensureProofLoaded() || solverUnion == SolverTypeCollection.EMPTY_COLLECTION) {
            mainWindow.popupWarning("No proof loaded or no solvers selected.", "Oops...");
            return;
        }
        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            // The preconditions {@code ensureProofLoaded()} and the non-empty solver union were
            // already checked above; a missing proof here is a concurrent state change,
            // crash-equivalent to the previous NPE.
            throw new NullPointerException("No proof loaded for SMT solving.");
        }

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
    public boolean equals(@Nullable Object obj) {
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
