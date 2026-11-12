/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import java.util.List;
import javafx.geometry.Insets;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.SelectionMode;
import javafx.scene.text.Font;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.AuxiliaryContract;

/**
 * contractcompletions (P2b): JavaFX port of the abstract Swing
 * {@code AuxiliaryContractSelectionPanel<T>} (AuxiliaryContractSelectionPanel.java, 124 lines)
 * — the single-selection list of auxiliary contracts (block/loop contracts) rendered as titled
 * cells with the contract's plain text (Swing renders {@code getHtmlText}; the HTML styling is
 * dropped, see {@link ContractSelectionPanelF}).
 */
public abstract class AuxiliaryContractSelectionPanelF<T extends AuxiliaryContract>
        extends ListView<T> {

    protected final Services services;

    /** re-entrancy guard for the keep-selection listener (see the constructor). */
    private boolean selectionGuard;

    protected AuxiliaryContractSelectionPanelF(final Services services,
            final boolean multipleSelection) {
        this.services = services;
        getSelectionModel().setSelectionMode(
            multipleSelection ? SelectionMode.MULTIPLE : SelectionMode.SINGLE);
        // Swing: an emptying selection keeps the previously selected index
        getSelectionModel().getSelectedItems()
                .addListener((javafx.collections.ListChangeListener<T>) change -> {
                    if (selectionGuard) {
                        return;
                    }
                    if (getSelectionModel().getSelectedItems().isEmpty() && !getItems().isEmpty()) {
                        selectionGuard = true;
                        try {
                            getSelectionModel().select(0);
                        } finally {
                            selectionGuard = false;
                        }
                    }
                });
        setCellFactory(view -> new AuxiliaryContractCell());
        getStyleClass().add("contract-selection-panel");
        setPrefSize(700, 500);
    }

    /** Swing {@code setContracts(T[], String)}. */
    public void setContracts(final T[] contracts, final String title) {
        getItems().setAll(contracts);
        getSelectionModel().select(0);
    }

    /** Swing {@code getContract}. */
    public T getContract() {
        List<T> selection = getSelectionModel().getSelectedItems();
        return computeContract(services, selection);
    }

    /** Swing {@code computeContract(Services, List<T>)} (implemented by the concrete panel). */
    public abstract T computeContract(Services services, List<T> selection);

    /** The FX cell, see the class javadoc. */
    private final class AuxiliaryContractCell extends javafx.scene.control.ListCell<T> {
        @Override
        protected void updateItem(T item, boolean empty) {
            super.updateItem(item, empty);
            if (empty || item == null) {
                setText(null);
                setGraphic(null);
                return;
            }
            Label nameLabel = new Label(item.getDisplayName());
            nameLabel.getStyleClass().add("contract-cell-name");
            nameLabel.setFont(Font.font(Font.getDefault().getFamily(),
                javafx.scene.text.FontWeight.BOLD, 12));
            Text body = new Text(item.getPlainText(services));
            body.getStyleClass().add("contract-cell-text");
            javafx.scene.layout.VBox box =
                new javafx.scene.layout.VBox(nameLabel, new TextFlow(body));
            box.setPadding(new Insets(2));
            box.getStyleClass().add("contract-cell");
            setText(null);
            setGraphic(box);
        }
    }
}
