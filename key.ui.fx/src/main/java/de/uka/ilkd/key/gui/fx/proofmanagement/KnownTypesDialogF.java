/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.proofmanagement;

import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;

/**
 * menu: modal dialog showing the type hierarchy known to a proof (Swing
 * {@code ShowKnownTypesAction.showTypeHierarchy}, ShowKnownTypesAction.java:47-83): a "Package
 * view" tab with the {@link ClassTreeF} of the proof's services in a scroll pane and an OK button
 * that closes the dialog (default button, Escape closes too). Window title "Known types for this
 * proof", 300×400 like the Swing original, centered on the owner.
 */
public final class KnownTypesDialogF extends javafx.stage.Stage {

    private KnownTypesDialogF(Window owner, Proof proof) {
        setTitle("Known types for this proof");
        initOwner(owner);
        if (owner != null) {
            // Swing: new JDialog(mainWindow, title, true) — modal to the owner window
            initModality(Modality.WINDOW_MODAL);
        }

        TabPane tabbedPane = new TabPane();
        ScrollPane scroll = new ScrollPane(new ClassTreeF(false, false, proof.getServices()));
        scroll.setFitToWidth(true);
        tabbedPane.getTabs().add(new Tab("Package view", scroll));

        Button okButton = new Button("OK");
        okButton.setOnAction(e -> close());
        ButtonBar.setButtonData(okButton, ButtonBar.ButtonData.OK_DONE);
        okButton.setDefaultButton(true);
        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().add(okButton);
        BorderPane.setMargin(buttonBar, new Insets(10));

        BorderPane root = new BorderPane(tabbedPane, null, null, buttonBar, null);
        Scene scene = new Scene(root, 300, 400);
        ThemeManager.getInstance().manage(scene);
        // Swing: GuiUtilities.attachClickOnEscListener(okButton) closes with Escape
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                close();
                e.consume();
            }
        });
        setScene(scene);
    }

    /**
     * Opens the known-types dialog for the given proof (Swing
     * {@code ShowKnownTypesAction.showTypeHierarchy}, ShowKnownTypesAction.java:47-83; modal, 300
     * × 400, centered on the owner).
     *
     * @param owner the owner window (the main window stage); may be {@code null}
     * @param proof the selected proof, must not be {@code null} (the menu item is disabled
     *        without a proof)
     */
    public static void show(Window owner, Proof proof) {
        KnownTypesDialogF dialog = new KnownTypesDialogF(owner, proof);
        if (owner != null) {
            dialog.setOnShown(e -> {
                // center over the owner like Swing setLocationRelativeTo(mainWindow)
                dialog.setX(owner.getX() + owner.getWidth() / 2 - dialog.getWidth() / 2);
                dialog.setY(owner.getY() + owner.getHeight() / 2 - dialog.getHeight() / 2);
            });
        }
        dialog.showAndWait();
    }
}
