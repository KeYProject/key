/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.Collection;
import java.util.Map;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * menu: dialog showing the active settings of the selected proof (Swing
 * {@code ShowActiveSettingsAction}, a debugging window over
 * {@code SettingsTreeModel(proof.getSettings(), ProofIndependentSettings.DEFAULT_INSTANCE)}).
 * <p>
 * This is a coarse port of the Swing tree: the {@link TreeView} renders the proof-dependent
 * settings ({@code proof.getSettings().asConfiguration()}) and the proof-independent settings
 * ({@code ProofIndependentSettings.asConfiguration()}) as a sectioned configuration tree, plus
 * the announce line with the proof name. Title and structure mirror the Swing
 * {@code ViewSettingsDialog} ("All active settings").
 * <p>
 * // menu: KNOWN-DEFERRED — Swing {@code SettingsTreeModel} renders each section with
 * OptionContentNode components (real Swing editors per option); the FX port shows the plain
 * key: value leaves instead. The "Taclet Options" deep-link of
 * {@code ShowActiveSettingsAction.showAndFocusTacletOptions} is not ported either (no Swing
 * call site uses it besides the old menu entry it replaced).
 */
public final class ActiveSettingsDialogF extends javafx.stage.Stage {

    private ActiveSettingsDialogF(Window owner, Proof proof) {
        setTitle("All active settings");
        initOwner(owner);
        if (owner != null) {
            // Swing: JDialog(owner frame, ...) — window-modal
            initModality(Modality.WINDOW_MODAL);
        }

        // Swing announce label (ShowActiveSettingsAction.java:78-85)
        Label announce = new Label("This shows the active settings for the proof: " + proof.name()
            + ".\nTo change settings for future proofs, use Options > Show Settings.");
        announce.setWrapText(true);
        announce.setPadding(new Insets(5));

        TreeView<String> tree = new TreeView<>(settingsTree(proof));
        tree.setShowRoot(true);
        tree.setPrefSize(420, 320);

        Button okButton = new Button("OK");
        okButton.setOnAction(e -> close());
        ButtonBar.setButtonData(okButton, ButtonBar.ButtonData.OK_DONE);
        okButton.setDefaultButton(true);
        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().add(okButton);
        BorderPane.setMargin(buttonBar, new Insets(10));

        ScrollPane scroll = new ScrollPane(tree);
        scroll.setFitToWidth(true);

        BorderPane root = new BorderPane();
        root.setTop(announce);
        root.setCenter(scroll);
        root.setBottom(buttonBar);
        Scene scene = new Scene(root, 520, 460);
        ThemeManager.getInstance().manage(scene);
        // Swing: DISPOSE_ON_CLOSE + Escape closes (ShowActiveSettingsAction.java:95-96)
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                close();
                e.consume();
            }
        });
        setScene(scene);
    }

    /**
     * Builds the settings tree of the dialog (Swing {@code SettingsTreeModel.generateTree}): the
     * root "All Settings" holds the proof-dependent and the proof-independent sections, each a
     * sorted configuration tree like {@code SettingsTreeModel.configurationTable}.
     */
    private static TreeItem<String> settingsTree(Proof proof) {
        TreeItem<String> root = new TreeItem<>("All Settings");
        TreeItem<String> proofSection = new TreeItem<>("Proof Settings");
        proofSection.getChildren()
                .addAll(configurationTree(proof.getSettings().asConfiguration()));
        // menu: KNOWN-DEFERRED — Swing's proof section renders an introductory
        // "These are the proof dependent settings." OptionContentNode; the plain tree carries
        // the configuration leaves directly.
        root.getChildren().add(proofSection);
        TreeItem<String> independentSection = new TreeItem<>("Proof-Independent Settings");
        independentSection.getChildren()
                .addAll(configurationTree(ProofIndependentSettings.DEFAULT_INSTANCE
                        .asConfiguration()));
        root.getChildren().add(independentSection);
        root.setExpanded(true);
        proofSection.setExpanded(true);
        return root;
    }

    /**
     * One tree level per configuration section, values as {@code key: value} leaves (Swing
     * {@code SettingsTreeModel.configurationTable}, SettingsTreeModel.java:93-120).
     */
    private static java.util.List<TreeItem<String>> configurationTree(Configuration cfg) {
        java.util.List<TreeItem<String>> items = new java.util.ArrayList<>();
        for (String name : cfg.keys().stream().sorted().toList()) {
            Object value = cfg.get(name);
            if (value == null) {
                items.add(new TreeItem<>(" <not set>"));
            } else if (value instanceof Configuration nested) {
                TreeItem<String> node = new TreeItem<>(name);
                node.getChildren().addAll(configurationTree(nested));
                items.add(node);
            } else if (value instanceof Collection<?> col) {
                TreeItem<String> node = new TreeItem<>(name);
                col.forEach(e -> node.getChildren().add(new TreeItem<>(String.valueOf(e))));
                items.add(node);
            } else if (value instanceof Map<?, ?> map) {
                TreeItem<String> node = new TreeItem<>(name);
                map.forEach((k, v) -> node.getChildren()
                        .add(new TreeItem<>(k + ": " + v)));
                items.add(node);
            } else {
                items.add(new TreeItem<>(name + ": " + value));
            }
        }
        return items;
    }

    /**
     * Opens the active-settings dialog for the given proof (Swing
     * {@code ShowActiveSettingsAction.actionPerformed} → {@code ViewSettingsDialog},
     * ShowActiveSettingsAction.java:32-47; window-modal, centered on the owner).
     *
     * @param owner the owner window (the main window stage); may be {@code null}
     * @param proof the selected proof, must not be {@code null} (the menu item is disabled
     *        without a proof)
     */
    public static void show(Window owner, Proof proof) {
        ActiveSettingsDialogF dialog = new ActiveSettingsDialogF(owner, proof);
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
