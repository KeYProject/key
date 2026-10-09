/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.control.TextFormatter;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * menu: MP3a — JavaFX port of the Swing {@code ViewSelector}
 * (key.ui/.../gui/configuration/ViewSelector.java), opened by the View&gt;ToolTip Options… item
 * (Swing {@code ToolTipOptionsAction.actionPerformed} → {@code ViewSelector.mainWindow},
 * ToolTipOptionsAction.java:26). The dialog edits the tooltip options of the
 * {@linkplain ViewSettings proof-independent view settings}:
 * <ul>
 * <li>the maximum line count of the tooltips of applicable rules with schema-variable
 * instantiations (Swing {@code NumberInputField}, digits only; on parse failure OK resets the
 * value to the previously stored one instead of applying garbage),</li>
 * <li>"show uninstantiated taclet" (Swing {@code showUninstantiatedTacletCB},
 * {@code ViewSettings.getShowUninstantiatedTaclet}),</li>
 * <li>"pretty-print whole Taclet" (Swing {@code showWholeTacletCB},
 * {@code ViewSettings.getShowWholeTaclet}).</li>
 * </ul>
 * The Swing "Save as Default" button (persisting via {@code ProofIndependentSettings.saveSettings})
 * is deliberately not ported — the default settings are written by the FX settings dialog
 * (SettingsManagerF), which exposes the same options.
 */
public final class ToolTipOptionsDialogF extends javafx.stage.Stage {

    private ToolTipOptionsDialogF(Window owner) {
        setTitle("Maximum line number for tooltips");
        initOwner(owner);
        if (owner != null) {
            // Swing: JDialog(parent, title, true) — window-modal
            initModality(Modality.WINDOW_MODAL);
        }

        ViewSettings viewSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        int maxLines = viewSettings.getMaxTooltipLines();
        boolean showWholeTaclet = viewSettings.getShowWholeTaclet();
        boolean showUninstantiatedTaclet = viewSettings.getShowUninstantiatedTaclet();

        Label maxLinesLabel = new Label("Maximum size (line count) of the tooltips of applicable"
            + " rules\n with schema variable instantiations displayed. In case of longer\n"
            + " tooltips the instantiation will be suppressed.");
        TextField maxLinesField = new TextField(String.valueOf(maxLines));
        // digits only, like the Swing NumberInputField (ViewSelector.NumberDocument:165-175)
        maxLinesField.setTextFormatter(new TextFormatter<String>(
            change -> change.getControlNewText().matches("\\d*")
                    ? change
                    : null));
        HBox maxLinesRow = new HBox(8, maxLinesLabel, maxLinesField);

        CheckBox showUninstantiatedTacletBox =
            new CheckBox("show uninstantiated taclet recommended for unexperienced users");
        showUninstantiatedTacletBox.setSelected(showUninstantiatedTaclet);
        CheckBox showWholeTacletBox = new CheckBox(
            "pretty-print whole Taclet including 'name', 'find', 'varCond' and 'heuristics'");
        showWholeTacletBox.setSelected(showWholeTaclet);

        GridPane center = new GridPane();
        center.setHgap(8);
        center.setVgap(10);
        center.add(maxLinesRow, 0, 0);
        center.add(showUninstantiatedTacletBox, 0, 1);
        center.add(showWholeTacletBox, 0, 2);
        center.setPadding(new Insets(12));

        Button okButton = new Button("OK");
        okButton.setDefaultButton(true);
        // Swing OK: parse the field, write all three settings back, close
        // (ViewSelector.java:99-115).
        // Integer.parseInt throws on invalid input; like Swing's intended behavior the value then
        // falls back to the previously stored setting instead of being applied.
        okButton.setOnAction(e -> {
            int maxSteps;
            try {
                maxSteps = Integer.parseInt(maxLinesField.getText());
            } catch (NumberFormatException nfe) {
                maxSteps = viewSettings.getMaxTooltipLines();
            }
            viewSettings.setMaxTooltipLines(maxSteps);
            viewSettings.setShowWholeTaclet(showWholeTacletBox.isSelected());
            viewSettings.setShowUninstantiatedTaclet(showUninstantiatedTacletBox.isSelected());
            close();
        });
        Button cancelButton = new Button("Cancel");
        // Swing Cancel: close without writing (ViewSelector.java:133-137)
        cancelButton.setOnAction(e -> close());
        ButtonBar.setButtonData(okButton, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(cancelButton, ButtonBar.ButtonData.CANCEL_CLOSE);
        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().addAll(okButton, cancelButton);
        BorderPane.setMargin(buttonBar, new Insets(10));

        BorderPane root = new BorderPane();
        root.setCenter(center);
        root.setBottom(buttonBar);
        Scene scene = new Scene(root, 620, 170);
        ThemeManager.getInstance().manage(scene);
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                close();
                e.consume();
            }
        });
        setScene(scene);
    }

    /**
     * Shows the dialog (Swing {@code ViewSelector.setVisible(true)}, ViewSelector.java:27).
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     */
    public static void show(Window owner) {
        new ToolTipOptionsDialogF(owner).show();
    }
}
