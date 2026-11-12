/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
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
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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
 * The Swing "Save as Default" button ({@code ViewSelector.java:116-130}: write the three
 * settings into {@code ProofIndependentSettings.DEFAULT_INSTANCE}, persist them via
 * {@code ProofIndependentSettings.saveSettings()} and close) is ported (A8, P3c) so the tooltip
 * defaults survive a restart — the {@link SettingsManagerF} settings dialog does not expose these
 * tooltip options, contrary to the earlier note.
 */
public final class ToolTipOptionsDialogF extends javafx.stage.Stage {

    private static final Logger LOGGER = LoggerFactory.getLogger(ToolTipOptionsDialogF.class);

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
            viewSettings.setMaxTooltipLines(
                parseMaxLines(maxLinesField, viewSettings));
            viewSettings.setShowWholeTaclet(showWholeTacletBox.isSelected());
            viewSettings.setShowUninstantiatedTaclet(showUninstantiatedTacletBox.isSelected());
            close();
        });
        Button saveButton = new Button("Save as Default");
        // A8 (P3c): the Swing "Save as Default" button (ViewSelector.java:116-130) — writes the
        // same three settings, persists them via ProofIndependentSettings.saveSettings() and
        // closes (the value survives a restart).
        saveButton.setOnAction(e -> {
            applyAsDefault(viewSettings, parseMaxLines(maxLinesField, viewSettings),
                showWholeTacletBox.isSelected(), showUninstantiatedTacletBox.isSelected());
            close();
        });
        Button cancelButton = new Button("Cancel");
        // Swing Cancel: close without writing (ViewSelector.java:133-137)
        cancelButton.setOnAction(e -> close());
        ButtonBar.setButtonData(okButton, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(cancelButton, ButtonBar.ButtonData.CANCEL_CLOSE);
        ButtonBar.setButtonData(saveButton, ButtonBar.ButtonData.LEFT);
        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().addAll(okButton, saveButton, cancelButton);
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

    /** Parses the numeric tooltip-line field; on invalid input the stored value is kept. */
    private static int parseMaxLines(TextField field, ViewSettings viewSettings) {
        try {
            return Integer.parseInt(field.getText());
        } catch (NumberFormatException nfe) {
            return viewSettings.getMaxTooltipLines();
        }
    }

    /**
     * A8 (P3c): writes the three tooltip options and persists them as default
     * (Swing {@code ViewSelector} Save as Default: {@code ProofIndependentSettings.saveSettings()},
     * ViewSelector.java:118-130).
     *
     * @param viewSettings the (proof-independent) view settings to write
     * @param maxLines parsed maximum tooltip line count
     * @param showWholeTaclet {@code showWholeTaclet} flag
     * @param showUninstantiatedTaclet {@code showUninstantiatedTaclet} flag
     */
    static void applyAsDefault(ViewSettings viewSettings, int maxLines, boolean showWholeTaclet,
            boolean showUninstantiatedTaclet) {
        ProofIndependentSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE;
        settings.getViewSettings().setMaxTooltipLines(maxLines);
        settings.getViewSettings().setShowWholeTaclet(showWholeTaclet);
        settings.getViewSettings().setShowUninstantiatedTaclet(showUninstantiatedTaclet);
        // temporary solution, stores more than wanted %%%% (comment kept from the Swing original)
        settings.saveSettings();
    }

    /**
     * A8 (P3c): self test of the "Save as Default" persistence behind the button — writes a
     * distinctive value, verifies that the settings file on disk contains it, and restores the
     * previous values (also persisted, so the test leaves no trace).
     *
     * @return a self-test report ending in {@code PASS} or {@code FAIL}
     */
    public static String verifySaveAsDefault() {
        ProofIndependentSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE;
        ViewSettings viewSettings = settings.getViewSettings();
        int originalMax = viewSettings.getMaxTooltipLines();
        boolean originalWhole = viewSettings.getShowWholeTaclet();
        boolean originalUninst = viewSettings.getShowUninstantiatedTaclet();
        try {
            int testValue = originalMax == 4242 ? 4243 : 4242;
            applyAsDefault(viewSettings, testValue, !originalWhole, !originalUninst);
            // the persisted file is the .json (or the legacy .props) proof-independent settings
            Path settingsPath = PathConfig.currentPaths.proofIndependentSettings;
            if (!Files.exists(settingsPath)) {
                settingsPath = settingsPath.resolveSibling(
                    settingsPath.getFileName().toString().replace(".json", ".props"));
            }
            String content = Files.exists(settingsPath) ? Files.readString(settingsPath) : "";
            boolean persisted = content.contains(String.valueOf(testValue));
            String verdict = persisted ? "PASS" : "FAIL";
            return "save-as-default value=" + testValue + " persisted=" + persisted
                + " file=" + settingsPath + " " + verdict;
        } catch (IOException e) {
            LOGGER.warn("Save-as-default self test failed", e);
            return "Save-as-default self test failed: " + e.getMessage() + " FAIL";
        } finally {
            viewSettings.setMaxTooltipLines(originalMax);
            viewSettings.setShowWholeTaclet(originalWhole);
            viewSettings.setShowUninstantiatedTaclet(originalUninst);
            settings.saveSettings();
        }
    }
}
