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
import de.uka.ilkd.key.speclang.AuxiliaryContract;

import org.key_project.util.javafx.FxUtil;

/**
 * contractcompletions (P2b): JavaFX port of the generic Swing
 * {@code AuxiliaryContractConfigurator<T>} (AuxiliaryContractConfigurator.java, 123 lines) — a
 * modal dialog wrapping an injected {@link AuxiliaryContractSelectionPanelF} with OK/Cancel,
 * double-click = OK and Escape = Cancel. Used by the block contract completions (Swing
 * BlockContractInternal/ExternalCompletion with the {@code BlockContractSelectionPanel}).
 * <p>
 * Deviation: application modality without owner, see {@link ContractConfiguratorF}.
 */
public class AuxiliaryContractConfiguratorF<T extends AuxiliaryContract> {

    private final Stage stage = new Stage();
    private final AuxiliaryContractSelectionPanelF<T> contractPanel;
    private boolean successful = false;

    /**
     * Swing constructor ({@code name} = dialog title, {@code contractPanel} = the injected
     * panel, {@code contracts}/{@code title} for the panel). Call {@link #show()} to display.
     */
    public AuxiliaryContractConfiguratorF(final String name,
            final AuxiliaryContractSelectionPanelF<T> contractPanel,
            final Services services, final T[] contracts, final String title) {
        this.contractPanel = contractPanel;
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
        stage.setTitle(name);
        stage.setScene(scene);
    }

    /** Shows the dialog modally and blocks until it is closed. */
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

    /** Swing {@code getContract}. */
    public T getContract() {
        return contractPanel.getContract();
    }
}
