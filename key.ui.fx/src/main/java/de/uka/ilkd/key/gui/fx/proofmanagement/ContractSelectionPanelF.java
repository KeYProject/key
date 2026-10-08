/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.proofmanagement;

import java.util.Comparator;
import java.util.List;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.geometry.Insets;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * A titled list panel for selecting a single {@link Contract}, port of {@code
 * de.uka.ilkd.key.gui.ContractSelectionPanel} (key.ui) reduced to the behavior the proof
 * management dialog needs (ContractSelectionPanel.java:66-127, 250-320):
 * <ul>
 * <li>{@link #setContracts(ImmutableSet, String)} sorts by contract type, then display name, then
 * id (ContractSelectionPanel.java:36-43, 260-287) and preselects the first entry
 * (ContractSelectionPanel.java:284);</li>
 * <li>{@link #getContract()} returns the selected contract or {@code null} if the selection is
 * empty (ContractSelectionPanel.java:314-320; the multi-selection combination of
 * ContractSelectionPanel.java:297-306 is not ported — the proof management dialog always uses
 * single selection);</li>
 * <li>{@link #selectContract(Contract)} selects the given contract
 * (ContractSelectionPanel.java:308-312);</li>
 * <li>each cell shows the display name as the heading and the plain-text rendering of the
 * contract (ContractSelectionPanel.java:154-190 uses {@code getHTMLText};
 * {@code getPlainText} is the HTML-free equivalent).</li>
 * </ul>
 * Not ported: the auxiliary-contract graying (ContractSelectionPanel.java:104-142, 171-183 —
 * needs the closed-proof/used-contract fixpoint computation) and the multiple selection mode.
 */
public final class ContractSelectionPanelF extends VBox {

    /**
     * The contract sort order of the Swing original: by contract type
     * (CONTRACT_TYPE_ORDER, ContractSelectionPanel.java:36-43), then display name, then id
     * (ContractSelectionPanel.java:260-287).
     */
    private static final Comparator<Contract> CONTRACT_ORDER = Comparator
            .comparingInt(ContractSelectionPanelF::typeOrder)
            .thenComparing(Contract::getDisplayName)
            .thenComparingInt(Contract::id);

    /** ranks the contract types (Swing CONTRACT_TYPE_ORDER, ContractSelectionPanel.java:36-43). */
    private static int typeOrder(Contract c) {
        // Contract.getTypeName() returns e.g. "JML operation contract"; the ranking mirrors
        // Swing's class-based map (FunctionalOperation < InformationFlow < Dependency <
        // BlockContract < LoopContract)
        return switch (c.getTypeName()) {
            case "JML operation contract" -> 0;
            case "JML information flow contract" -> 1;
            case "JML dependency contract" -> 2;
            case "block contract" -> 3;
            case "loop contract" -> 4;
            default -> 100;
        };
    }

    /** the services used to render the contract text (Swing {@code services}, :45). */
    private final Services services;

    /** the bordered title above the list (Swing TitledBorder, :72). */
    private final Label title = new Label("Contracts");

    /** the contract list (Swing JList&lt;Contract&gt;, :80). */
    private final ListView<Contract> contractList = new ListView<>();

    /** notified on every selection change (Swing addListSelectionListener, :252-254). */
    private final ChangeListener<Contract> selectionListener;

    /** the currently shown contracts (Swing {@code contracts}, :48). */
    private List<Contract> contracts = List.of();

    /**
     * Creates the panel with the default title "Contracts".
     *
     * @param services the services of the proof environment (used to render contract text)
     * @param selectionListener notified on every selection change
     */
    public ContractSelectionPanelF(Services services,
            ChangeListener<Contract> selectionListener) {
        this.services = services;
        this.selectionListener = selectionListener;
        setSpacing(2);
        setPadding(new Insets(4, 8, 4, 8));
        title.getStyleClass().add("dialog-section-title");
        contractList.setPlaceholder(new Label("(none)"));
        contractList.setCellFactory(view -> new ListCell<>() {
            @Override
            protected void updateItem(Contract item, boolean empty) {
                super.updateItem(item, empty);
                if (empty || item == null) {
                    setText(null);
                    setGraphic(null);
                } else {
                    // the display name as the bold heading, the plain text rendering below
                    // (Swing cell renderer, ContractSelectionPanel.java:154-190)
                    var heading = new Label(item.getDisplayName());
                    heading.getStyleClass().add("contract-cell-name");
                    var text = new Label(item.getPlainText(services));
                    text.setWrapText(true);
                    text.getStyleClass().add("contract-cell-text");
                    text.setMaxWidth(Double.MAX_VALUE);
                    var box = new VBox(2, heading, text);
                    box.getStyleClass().add("contract-cell");
                    setText(null);
                    setGraphic(box);
                }
            }
        });
        contractList.getSelectionModel().selectedItemProperty()
                .addListener(this::fireSelection);
        getChildren().addAll(title, contractList);
        VBox.setVgrow(contractList, Priority.ALWAYS);
    }

    /** forwards the selection change to the listener (Swing list selection event). */
    private void fireSelection(ObservableValue<? extends Contract> obs, Contract oldV,
            Contract newV) {
        selectionListener.changed(obs, oldV, newV);
    }

    /**
     * Shows the given contracts under the given title (Swing
     * {@code setContracts(ImmutableSet, String)}, ContractSelectionPanel.java:290-293): sorted
     * and with the first entry preselected (ContractSelectionPanel.java:284).
     */
    public void setContracts(ImmutableSet<Contract> newContracts, @Nullable String newTitle) {
        contracts = newContracts == null ? List.of()
                : newContracts.stream().sorted(CONTRACT_ORDER).toList();
        title.setText(newTitle == null ? "Contracts" : newTitle);
        contractList.getSelectionModel().clearSelection();
        contractList.getItems().setAll(contracts);
        if (!contracts.isEmpty()) {
            contractList.getSelectionModel().selectFirst();
        }
    }

    /**
     * @return the selected contract or {@code null} if the selection is empty (Swing
     *         {@code getContract}, ContractSelectionPanel.java:314-320 — single selection only)
     */
    public @Nullable Contract getContract() {
        return contractList.getSelectionModel().getSelectedItem();
    }

    /**
     * Selects the given contract in the list (Swing {@code selectContract},
     * ContractSelectionPanel.java:308-312); {@code null} clears the selection.
     */
    public void selectContract(@Nullable Contract contract) {
        if (contract == null) {
            contractList.getSelectionModel().clearSelection();
        } else {
            contractList.getSelectionModel().select(contract);
        }
    }

    /**
     * Selects the given contract and reports it to the selection listener — used when the dialog
     * restores a remembered selection while the panel is still empty and the change must also
     * refresh the start button (Swing ProofManagementDialog.select(ContractId) relies on the
     * JList's selection events, ProofManagementDialog.java:403-408).
     */
    public void selectContractAndNotify(@Nullable Contract contract) {
        selectContract(contract);
        if (contract != null) {
            selectionListener.changed(null, null, contract);
        }
    }

    /** @return the contracts currently shown (empty if none) */
    public List<Contract> getContracts() {
        return contracts;
    }
}
