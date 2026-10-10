/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.stage.Modality;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.util.javafx.FxUtil;

/**
 * contractcompletions (P2b): JavaFX port of the Swing {@code ContractConfigurator}
 * (ContractConfigurator.java, 130 lines) — the modal dialog wrapping a
 * {@link ContractSelectionPanelF} with OK/Cancel. The "apply back" is done by the completion
 * (Swing: the dialog only exposes {@code wasSuccessful()}/{@code getContract()}).
 * <p>
 * Deviation: the Swing dialog is a modal {@code JDialog} with {@code MainWindow} as owner (the
 * dialog shows with WINDOW modality); the FX dialog uses application modality with no owner
 * (the pattern of the already-ported {@code MergePartnerSelectionDialogF}). Double-click on the
 * list and Escape behave like in Swing ({@code GuiUtilities.attachClickOnEscListener}).
 */
public class ContractConfiguratorF {

    private final Stage stage = new Stage();
    private final ContractSelectionPanelF contractPanel;
    private boolean successful = false;

    /**
     * Creates the dialog; call {@link #show()} to show it modally (Swing: the constructor shows
     * the modal dialog immediately — the FX port splits construction and display like
     * {@code MergePartnerSelectionDialogF} so the dialog can also be driven by the
     * {@code key.fx.verify.*} hooks).
     *
     * @param services the services
     * @param contracts the selectable contracts
     * @param title the list title ("Contracts for ...")
     * @param allowMultipleContracts whether several (functional operation) contracts may be
     *        selected and combined
     */
    public ContractConfiguratorF(Services services, Contract[] contracts, String title,
            boolean allowMultipleContracts) {
        contractPanel = new ContractSelectionPanelF(services, allowMultipleContracts);
        contractPanel.setContracts(contracts, title);

        Button okButton = new Button("OK");
        okButton.setOnAction(e -> {
            successful = true;
            stage.close();
        });
        Button cancelButton = new Button("Cancel");
        cancelButton.setOnAction(e -> {
            successful = false;
            stage.close();
        });
        HBox buttonPanel = new HBox(5, okButton, cancelButton);
        buttonPanel.setAlignment(Pos.CENTER_RIGHT);
        buttonPanel.setPadding(new Insets(5));

        BorderPane root = new BorderPane();
        root.setCenter(contractPanel);
        root.setBottom(buttonPanel);
        Scene scene = new Scene(root, 820, 560);
        ThemeManager.getInstance().style(scene);
        // Swing: double-click on the list = OK
        contractPanel.setOnMouseClicked(e -> {
            if (e.getClickCount() == 2) {
                successful = true;
                stage.close();
            }
        });
        // Swing: GuiUtilities.attachClickOnEscListener(cancelButton)
        scene.getAccelerators().put(new KeyCodeCombination(KeyCode.ESCAPE), () -> {
            successful = false;
            stage.close();
        });
        stage.setTitle("Contract Configurator");
        stage.setScene(scene);
    }

    /**
     * Shows the dialog modally and blocks until it is closed (Swing: the modal
     * {@code setVisible(true)} on the EDT).
     */
    public void show() {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(this::show);
            return;
        }
        stage.initModality(Modality.APPLICATION_MODAL);
        stage.showAndWait();
    }

    /** Non-blocking variant for the {@code key.fx.verify.*} hooks. */
    public void showNonBlocking() {
        stage.initModality(Modality.NONE);
        stage.show();
    }

    /** Closes the dialog as if OK had been pressed (verification harness). */
    public void requestOk() {
        successful = true;
        stage.close();
    }

    /** Closes the dialog as if Cancel had been pressed (verification harness). */
    public void requestCancel() {
        successful = false;
        stage.close();
    }

    /** @return the stage (verification harness) */
    public Stage getStage() {
        return stage;
    }

    /** Swing {@code wasSuccessful}. */
    public boolean wasSuccessful() {
        return successful;
    }

    /** Swing {@code getContract}: the selected (possibly combined) contract. */
    public Contract getContract() {
        return contractPanel.getContract();
    }
}
