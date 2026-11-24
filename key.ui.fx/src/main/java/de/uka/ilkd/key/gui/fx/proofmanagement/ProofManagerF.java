/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.proofmanagement;

import java.util.function.Consumer;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The multi-proof state of the JavaFX main window (proofmgmt): the list of currently loaded
 * proofs and the active one. The Swing UI keeps this state in the {@code TaskTreeModel} of the
 * {@code TaskTree} view plus {@code MainWindow.getCurrentlyOpenedProofs} (TaskTree.java:112-123
 * registers every proof of a loaded aggregate); here the state lives in its own small class so
 * that {@code MainWindowF} and the {@code TaskTreeF} view both consult it, and so that proofs
 * started by the {@link ProofManagementDialogF} are registered at the same place.
 * <p>
 * The list holds the individual {@link Proof}s (for the common single-proof aggregates, Swing
 * {@code TaskTree.addProof} iterates {@code ProofAggregate.getProofs}, TaskTree.java:112-123).
 * Proof removal (Swing {@code TaskTree.removeProof}/{@code removeTask}, TaskTree.java:125-150)
 * is deferred until the Abandon-Task flow lands; {@link #removeProof(Proof)} is provided for the
 * future caller.
 */
public final class ProofManagerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofManagerF.class);

    /** the loaded proofs, in load order (Swing TaskTreeModel, newest task last). */
    private final ObservableList<Proof> proofs = FXCollections.observableArrayList();

    /**
     * The active proof. This mirrors the selection model of the mediator (the Swing
     * {@code TaskTree} highlights the row of {@code mediator.getSelectedProof},
     * TaskTree.java:397-415): updated by {@link #setActive(Proof)} (user clicks in the view /
     * the proof management dialog) and by the selection listener of the view.
     */
    private final ObjectProperty<Proof> activeProof = new SimpleObjectProperty<>(this,
        "activeProof");

    /**
     * Activates a proof in the main window; set by {@code MainWindowF} to
     * {@code selectionModel::setSelectedProof} (the Swing TaskTree click routes through
     * {@code KeYSelectionModel.setSelectedProof} too, TaskTree.java:194-200). Kept as a
     * callback so this class has no dependency on the FX mediator.
     */
    private @Nullable Consumer<Proof> activationHandler;

    /**
     * @return the loaded proofs (observable; the Loaded Proofs view binds to it)
     */
    public ObservableList<Proof> proofs() {
        return proofs;
    }

    /** @return the active proof or {@code null} */
    public @Nullable Proof getActiveProof() {
        return activeProof.get();
    }

    /** @return the observable active proof */
    public ReadOnlyObjectProperty<Proof> activeProofProperty() {
        return activeProof;
    }

    /**
     * Sets the handler activating a proof in the main window (the selection model switch).
     *
     * @param handler called by {@link #setActive(Proof)}
     */
    public void setActivationHandler(@Nullable Consumer<Proof> handler) {
        this.activationHandler = handler;
    }

    /**
     * Registers a loaded proof (Swing {@code TaskTree.addProof}, TaskTree.java:112-123).
     * No-op if the proof is already registered (a re-loaded quick save re-registers).
     *
     * @param proof the loaded proof
     */
    public void addProof(Proof proof) {
        if (proofs.contains(proof)) {
            LOGGER.debug("Proof management: proof {} already registered", proof.name());
            return;
        }
        proofs.add(proof);
        LOGGER.info("Proof management: registered proof {} ({} total)", proof.name(),
            proofs.size());
    }

    /**
     * Unregisters a proof (Swing {@code TaskTree.removeProof}, TaskTree.java:241-267); no caller
     * yet (the Abandon-Task flow is deferred).
     *
     * @param proof the proof to remove, may be {@code null}
     */
    public void removeProof(@Nullable Proof proof) {
        if (proof != null) {
            proofs.remove(proof);
        }
    }

    /** @return whether the given proof is registered */
    public boolean contains(Proof proof) {
        return proofs.contains(proof);
    }

    /**
     * Activates the given proof (Swing {@code TaskTree.problemChosen}: the click switches the
     * mediator's selected proof, TaskTree.java:194-200): updates {@link #activeProofProperty()}
     * and routes the switch through the activation handler.
     *
     * @param proof the proof to make the active one
     */
    public void setActive(Proof proof) {
        activeProof.set(proof);
        if (activationHandler != null) {
            activationHandler.accept(proof);
        }
    }

    /**
     * Mirrors an activation that happened elsewhere (e.g. a load selecting the new proof)
     * without routing back through the activation handler.
     *
     * @param proof the newly active proof
     */
    public void setActiveFromSelection(@Nullable Proof proof) {
        activeProof.set(proof);
    }
}
