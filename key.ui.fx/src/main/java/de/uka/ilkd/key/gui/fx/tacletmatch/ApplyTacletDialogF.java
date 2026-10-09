/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.control.InstantiationFileHandler;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Common superclass for the JavaFX taclet-instantiation dialogs. It owns the shared {@link
 * TacletInstantiationModel}s and the Apply/Cancel buttons and carries the apply semantics shared by
 * both Swing dialogs ({@code de.uka.ilkd.key.gui.ApplyTacletDialog} of module {@code key.ui} and
 * its subclasses {@code TacletMatchDialog} / {@code classic.TacletMatchCompletionDialog}: push all
 * input to the model, build the {@link TacletApp}, apply it interactively on the goal, save the
 * instantiation list and close — or report the failure).
 *
 * <p>
 * The Swing base class additionally requests modal access to the mediator
 * ({@code mediator.requestModalAccess}) which suspends proof automation while the dialog is open
 * and frees it again on close. The JavaFX mediator has no modal-access mechanism yet; until then
 * the Apply button is simply disabled while an auto mode run is active (see {@link
 * #setAutoModeRunning(boolean)}), which is the observable part of the Swing semantics.
 */
public abstract class ApplyTacletDialogF extends Stage {

    private static final Logger LOGGER = LoggerFactory.getLogger(ApplyTacletDialogF.class);

    // buttons
    protected final Button cancelButton = new Button("Cancel");
    protected final Button applyButton = new Button("Apply");

    protected final TacletInstantiationModel[] model;

    /**
     * the proof control the application is performed with (Swing resolves it via {@code
     * mediator().getUI().getProofControl()})
     */
    protected final ProofControl proofControl;

    /** the goal the rule application is performed on */
    protected final Goal goal;

    protected ApplyTacletDialogF(Window owner, String title, TacletInstantiationModel[] model,
            ProofControl proofControl, Goal goal) {
        this.model = model;
        this.proofControl = proofControl;
        this.goal = goal;

        setTitle(title);
        cancelButton.setCancelButton(true);
        applyButton.setDefaultButton(true);
        cancelButton.setOnAction(e -> closeDialog());
        applyButton.setOnAction(e -> handleApply());
        setOnCloseRequest(e -> closeDialog());
        if (owner != null) {
            initOwner(owner);
        }
    }

    protected abstract void pushAllInputToModel();

    protected abstract int current();

    protected abstract void setStatus(String s);

    /**
     * Observable part of the Swing mediator's modal access: while an auto mode run is in progress
     * the rule application is refused by the core, so the Apply button is disabled.
     */
    public void setAutoModeRunning(boolean running) {
        applyButton.setDisable(running);
    }

    /**
     * The shared Apply semantics of the Swing {@code ButtonListener}s in {@code TacletMatchDialog}
     * and {@code classic.TacletMatchCompletionDialog} (both push all input, create the taclet app,
     * call {@code proofControl.applyInteractive}, save the instantiation list and close; on failure
     * an error dialog is shown).
     */
    protected void handleApply() {
        try {
            pushAllInputToModel();
            TacletApp app = model[current()].createTacletApp();
            if (app == null) {
                // Swing: JOptionPane "Could not apply rule" / "Rule Application Failure"
                Alert alert = new Alert(Alert.AlertType.ERROR, "Could not apply rule");
                alert.setTitle("Rule Application Failure");
                alert.setHeaderText(null);
                alert.showAndWait();
                return;
            }
            proofControl.applyInteractive(app, goal);
        } catch (Exception exc) {
            onApplyException(exc);
            return;
        }
        InstantiationFileHandler.saveListFor(model[current()]);
        closeDialog();
    }

    /**
     * reports a failed application attempt (Swing {@code IssueDialog.showExceptionDialog}): the
     * exception is logged and surfaced as an error toast; the classic dialog additionally focuses
     * the offending input (see {@code TacletMatchCompletionDialogF}).
     */
    protected void onApplyException(Exception exc) {
        LOGGER.error("Taclet application failed", exc);
        NotificationManagerF.getInstance()
                .notify("Taclet application failed: " + exc.getMessage(), Kind.ERROR);
    }

    /** Swing {@code closeDialog()}: frees the mediator and disposes the dialog. */
    protected void closeDialog() {
        closeDlg();
        close();
    }

    /**
     * Swing {@code closeDlg()}: frees the modal access to the mediator. The JavaFX mediator has no
     * modal access yet, so this is a no-op; the hook stays so the wiring at the control seam
     * (WindowUserInterfaceControlF) can call it symmetrically.
     */
    protected void closeDlg() {
    }
}
