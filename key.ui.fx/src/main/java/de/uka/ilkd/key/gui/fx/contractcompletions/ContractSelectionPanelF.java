/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.geometry.Insets;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.SelectionMode;
import javafx.scene.text.Font;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;

import de.uka.ilkd.key.informationflow.impl.InformationFlowContractImpl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContractImpl;
import de.uka.ilkd.key.speclang.FunctionalBlockContract;
import de.uka.ilkd.key.speclang.FunctionalLoopContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * contractcompletions (P2b): JavaFX port of the Swing {@code ContractSelectionPanel}
 * (ContractSelectionPanel.java, 328 lines) — the contract list of the contract configurator
 * dialog: contracts sorted by type and name, each rendered as a titled cell with the contract's
 * plain text (the Swing cell renders {@code getHTMLText}; the FX port renders the plain text in
 * a monospaced flow — the HTML styling is dropped, see KNOWN-SIMPLIFIED), and auxiliary
 * contracts not applied in a closed proof grayed out ({@code setGrayOutAuxiliaryContracts}).
 */
public class ContractSelectionPanelF extends ListView<Contract> {

    /** Swing CONTRACT_TYPE_ORDER (ContractSelectionPanel.java:47-53). */
    private static final Map<Class<?>, Integer> CONTRACT_TYPE_ORDER = new LinkedHashMap<>();
    static {
        CONTRACT_TYPE_ORDER.put(FunctionalOperationContractImpl.class, 0);
        CONTRACT_TYPE_ORDER.put(InformationFlowContractImpl.class, 1);
        CONTRACT_TYPE_ORDER.put(DependencyContractImpl.class, 2);
        CONTRACT_TYPE_ORDER.put(FunctionalBlockContract.class, 3);
        CONTRACT_TYPE_ORDER.put(FunctionalLoopContract.class, 4);
    }

    private final Services services;
    private final StringProperty title = new SimpleStringProperty("Contracts");

    /**
     * Whether an auxiliary contract is grayed out if it has not been applied in a proof for a
     * non-auxiliary contract (Swing {@code grayOutAuxiliaryContracts}).
     */
    private boolean grayOutAuxiliaryContracts = false;

    /** the contracts currently displayed, in display order (renderer dependency). */
    private Contract[] contracts = new Contract[0];

    /** re-entrancy guard for the keep-selection listener (see the constructor). */
    private boolean selectionGuard;

    public ContractSelectionPanelF(Services services, boolean multipleSelection) {
        this.services = services;
        getSelectionModel().setSelectionMode(
            multipleSelection ? SelectionMode.MULTIPLE : SelectionMode.SINGLE);
        // Swing: an emptying selection keeps the previously selected index
        getSelectionModel().getSelectedItems()
                .addListener((javafx.collections.ListChangeListener<Contract>) change -> {
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
        setCellFactory(view -> new ContractCell());
        getStyleClass().add("contract-selection-panel");
        setPrefSize(700, 500);
    }

    /** Swing {@code setGrayOutAuxiliaryContracts}. */
    public void setGrayOutAuxiliaryContracts(boolean grayOutAuxiliaryContracts) {
        this.grayOutAuxiliaryContracts = grayOutAuxiliaryContracts;
        refresh();
    }

    /** The titled border title (Swing TitledBorder; the title row is part of the dialog). */
    public StringProperty titleProperty() {
        return title;
    }

    /**
     * Swing {@code setContracts(Contract[], String)}: sorts by contract type then display name
     * then id, fills the list and selects the first entry (ContractSelectionPanel.java:242-286).
     *
     * @param contracts the contracts, may be {@code null} or empty (clears the list)
     * @param title the new title, may be {@code null} (keeps the current one)
     */
    public void setContracts(Contract[] contracts, String title) {
        if (contracts == null || contracts.length == 0) {
            this.contracts = new Contract[0];
            getItems().clear();
            return;
        }
        Arrays.sort(contracts, (c1, c2) -> {
            Integer o1 = CONTRACT_TYPE_ORDER.get(c1.getClass());
            Integer o2 = CONTRACT_TYPE_ORDER.get(c2.getClass());
            int res = 0;
            if (o1 != null && o2 != null) {
                res = o1 - o2;
            } else if (o1 != null) {
                return -1;
            } else if (o2 != null) {
                return 1;
            }
            if (res != 0) {
                return res;
            }
            res = c1.getDisplayName().compareTo(c2.getDisplayName());
            if (res == 0) {
                return c1.id() - c2.id();
            }
            return res;
        });
        this.contracts = contracts;
        getItems().setAll(contracts);
        getSelectionModel().select(0);
        if (title != null) {
            this.title.set(title);
        }
    }

    /** Swing {@code setContracts(ImmutableSet<Contract>, String)}. */
    public void setContracts(ImmutableSet<Contract> contracts, String title) {
        setContracts(contracts.toArray(new Contract[contracts.size()]), title);
    }

    /** Swing {@code selectContract}: selects the given contract and scrolls to it. */
    public void selectContract(Contract contract) {
        getSelectionModel().select(contract);
        scrollTo(getItems().indexOf(contract));
    }

    /** Swing {@code getContract}: the combined contract of the selection. */
    public Contract getContract() {
        List<Contract> selection = new ArrayList<>(getSelectionModel().getSelectedItems());
        return computeContract(services, selection);
    }

    /**
     * Swing {@code computeContract} (ContractSelectionPanel.java:308-327, also used by the KeY
     * IDE): no selection → null; one contract → it; several contracts → they must all be
     * functional operation contracts and are combined via the specification repository.
     *
     * @param services the services
     * @param selection the selected contracts
     * @return the combined contract or {@code null}
     */
    public static Contract computeContract(Services services, List<Contract> selection) {
        if (selection.isEmpty()) {
            return null;
        } else if (selection.size() == 1) {
            return selection.get(0);
        } else {
            ImmutableSet<FunctionalOperationContract> toCombine = DefaultImmutableSet.nil();
            for (Contract contract : selection) {
                if (contract instanceof FunctionalOperationContract) {
                    toCombine = toCombine.add((FunctionalOperationContract) contract);
                } else {
                    throw new IllegalStateException(
                        "Don't know how to combine contracts of kind " + contract.getClass()
                            + "\n" + "Contract:\n" + contract.getPlainText(services));
                }
            }
            return services.getSpecificationRepository().combineOperationContracts(toCombine);
        }
    }

    /**
     * Swing renderer's gray-out logic (ContractSelectionPanel.java:104-139): a contract is
     * grayed when it is auxiliary and was not applied (transitively, over the non-auxiliary
     * contracts of the list) in a closed proof.
     *
     * @param contract the rendered contract
     * @return {@code true} if the cell is grayed out
     */
    private boolean isGrayedOut(Contract contract) {
        if (!grayOutAuxiliaryContracts || !contract.isAuxiliary()) {
            return false;
        }
        Set<Contract> appliedContracts = new HashSet<>();
        Set<Contract> consideredContracts = new HashSet<>();
        for (Contract c : contracts) {
            if (c.isAuxiliary()) {
                continue;
            }
            consideredContracts.add(c);
            Proof p = getClosedProof(c);
            if (p != null) {
                p.mgt().getUsedContracts().forEach(appliedContracts::add);
            }
        }
        int iterations = contracts.length - consideredContracts.size();
        for (int i = 0; i < iterations; ++i) {
            for (Contract c : contracts) {
                if (consideredContracts.contains(c) || !appliedContracts.contains(c)) {
                    continue;
                }
                consideredContracts.add(c);
                Proof p = getClosedProof(c);
                if (p != null) {
                    p.mgt().getUsedContracts().forEach(appliedContracts::add);
                }
            }
        }
        return !appliedContracts.contains(contract);
    }

    /** Swing {@code getClosedProof} (ContractSelectionPanel.java:198-208). */
    private Proof getClosedProof(Contract c) {
        ImmutableSet<Proof> proofs = services.getSpecificationRepository().getProofs(c);
        for (Proof proof : proofs) {
            if (proof.mgt().getStatus().getProofClosed()) {
                return proof;
            }
        }
        return null;
    }

    /**
     * The FX contract cell (Swing renderer, ContractSelectionPanel.java:92-193): a bordered box
     * with the bold display name on top and the plain contract text in a monospaced flow (the
     * Swing cell uses HTML text — the styling markup is dropped, see the class javadoc);
     * grayed-out auxiliary contracts use the {@code .contract-cell-gray} style class.
     */
    private final class ContractCell extends javafx.scene.control.ListCell<Contract> {
        @Override
        protected void updateItem(Contract item, boolean empty) {
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
            TextFlow flow = new TextFlow(body);
            javafx.scene.layout.VBox box =
                new javafx.scene.layout.VBox(nameLabel, flow);
            box.setPadding(new Insets(2));
            box.getStyleClass().add("contract-cell");
            if (isGrayedOut(item)) {
                box.getStyleClass().add("contract-cell-gray");
            }
            setText(null);
            setGraphic(box);
        }
    }
}
