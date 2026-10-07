/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.keyshortcuts;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.scene.Node;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyCombination.ModifierValue;
import javafx.scene.input.KeyEvent;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

/**
 * UI for configuring the keyboard shortcuts of the JavaFX UI, counter-part of
 * {@code de.uka.ilkd.key.gui.keyshortcuts.ShortcutSettings} of the Swing module {@code key.ui}.
 * <p>
 * The table lists the known actions of {@link KeyStrokeManagerF} (plus the unknown entries of the
 * shared {@code keystrokes.json}, which are shown without a description like in Swing) with the
 * shortcut in the last column. Editing the column opens a text field that captures the pressed
 * key combination directly from the {@link KeyEvent} (Swing's capture cell editor); the value is
 * stored and applied in the shared Swing {@code KeyStroke.toString()} format, e.g.
 * {@code "shift ctrl pressed P"} (displayed without the {@code "pressed"} token).
 * <p>
 * Duplicate shortcuts are highlighted with the error style and a tooltip instead of being
 * rejected: the duplicate check of the Swing original is commented out, so applying stays
 * possible (documented deviation).
 */
public class ShortcutSettingsF extends SettingsPanelF implements SettingsProviderF {

    private final TableView<ShortcutRow> tblShortcuts = new TableView<>();
    private final TableColumn<ShortcutRow, String> colName = new TableColumn<>("Name");
    private final TableColumn<ShortcutRow, String> colDescription =
        new TableColumn<>("Description");
    private final TableColumn<ShortcutRow, String> colShortcut = new TableColumn<>("Shortcut");

    public ShortcutSettingsF() {
        setHeaderText(getDescription());
        setSubHeaderText(
            "These settings are stored in " + KeyStrokeManagerF.SETTINGS_FILE.toAbsolutePath());

        colName.setCellValueFactory(
            data -> new SimpleStringProperty(shortName(data.getValue().actionId)));
        colDescription.setCellValueFactory(
            data -> new SimpleStringProperty(KeyStrokeManagerF.getInstance()
                    .descriptionOf(data.getValue().actionId).orElse("")));
        colShortcut.setCellValueFactory(data -> data.getValue().specProperty());
        colShortcut.setCellFactory(col -> new ShortcutCell());
        colName.setPrefWidth(260);
        colDescription.setPrefWidth(180);
        colShortcut.setPrefWidth(220);

        tblShortcuts.getColumns().setAll(colName, colDescription, colShortcut);
        tblShortcuts.setEditable(true);
        // sorted by name ascending, like the Swing TableRowSorter with the SortKey(0, ASCENDING)
        tblShortcuts.getSortOrder().add(colName);
        tblShortcuts.setColumnResizePolicy(
            TableView.CONSTRAINED_RESIZE_POLICY_FLEX_LAST_COLUMN);
        setCenter(tblShortcuts);
    }

    @Override
    public String getDescription() {
        return "Keyboard Shortcuts";
    }

    @Override
    public Node getPanel(MainWindowF window) {
        refresh();
        return this;
    }

    /**
     * Rebuilds the table model from the current {@link KeyStrokeManagerF} state (Swing
     * {@code ShortcutSettings.getPanel}); known bindings and the preserved unknown file entries
     * are merged and sorted by name.
     */
    private void refresh() {
        KeyStrokeManagerF manager = KeyStrokeManagerF.getInstance();
        TreeMap<String, String> entries = new TreeMap<>();
        for (Map.Entry<String, KeyCombination> entry : manager.getBindings().entrySet()) {
            entries.put(entry.getKey(), KeyStrokeManagerF.toSwingSpec(entry.getValue()));
        }
        entries.putAll(manager.getPersistedEntries());

        List<ShortcutRow> rows =
            entries.entrySet().stream().map(e -> new ShortcutRow(e.getKey(), e.getValue()))
                    .toList();
        tblShortcuts.setItems(FXCollections.observableList(rows));
        tblShortcuts.sort();
    }

    @Override
    public void apply(MainWindowF window) {
        KeyStrokeManagerF manager = KeyStrokeManagerF.getInstance();
        for (ShortcutRow row : tblShortcuts.getItems()) {
            String spec = row.spec.get() == null ? "" : row.spec.get();
            if (spec.equals(row.initialSpec)) {
                continue;
            }
            Optional<KeyCombination> combination = KeyStrokeManagerF.fromSwingSpec(spec);
            // an empty or unparseable entry removes the binding, so the default returns on the
            // next start (the Swing original writes an empty entry into the file instead)
            manager.bind(row.actionId, combination.orElse(null));
        }
        // the accelerators of the registered menu items are updated via KeyStrokeManagerF.bind
    }

    /**
     * @param actionId an action id (fully qualified class name of the Swing counterpart)
     * @return the action id without the common package prefixes (Swing
     *         {@code ShortcutsTableModel.getValueAt})
     */
    private static String shortName(String actionId) {
        return actionId.replaceAll("([a-z]\\w*\\.)*", "");
    }

    /**
     * The model row of one action.
     */
    private static class ShortcutRow {

        final String actionId;

        /** the spec at panel load time, for the change detection in {@link #apply} */
        final String initialSpec;

        /** the shortcut spec in the shared Swing format */
        final StringProperty spec = new SimpleStringProperty();

        ShortcutRow(String actionId, String spec) {
            this.actionId = actionId;
            this.initialSpec = spec;
            this.spec.set(spec);
        }

        StringProperty specProperty() {
            return spec;
        }
    }

    /**
     * The shortcut cell: shows the spec without the {@code "pressed"} token (for readability,
     * like the Swing model) and edits it in a text field that captures key combinations (Swing's
     * capture {@code DefaultCellEditor}). Duplicate specs are marked with the error style and a
     * tooltip.
     */
    private class ShortcutCell extends TableCell<ShortcutRow, String> {

        private final TextField editor = new TextField();

        ShortcutCell() {
            // the capture filter runs before the text field handles the key and consumes every
            // key press, so the pressed combination is captured like in Swing (the characters
            // the text field inserts on KEY_TYPED are cosmetic only, as in the Swing original)
            editor.addEventFilter(KeyEvent.KEY_PRESSED, this::capture);
            editor.focusedProperty().addListener((obs, was, focused) -> {
                if (!focused && isEditing()) {
                    // an emptied editor clears the binding, an untouched one reverts
                    if (editor.getText().isEmpty()) {
                        ShortcutRow row = getTableRow().getItem();
                        if (row != null) {
                            row.spec.set("");
                        }
                    }
                    cancelEdit();
                }
            });
        }

        @Override
        protected void updateItem(String item, boolean empty) {
            super.updateItem(item, empty);
            getStyleClass().remove("settings-input-error");
            setTooltip(null);
            if (empty || item == null) {
                setText(null);
                setGraphic(null);
                return;
            }
            ShortcutRow row = getTableRow().getItem();
            String clash = row == null ? null : duplicateOf(row);
            if (clash != null) {
                getStyleClass().add("settings-input-error");
                setTooltip(new Tooltip(
                    "Clash of key bindings: this shortcut is also used by " + clash));
            }
            setText(displayText(item));
        }

        @Override
        public void startEdit() {
            super.startEdit();
            ShortcutRow row = getTableRow().getItem();
            if (row == null) {
                return;
            }
            editor.setText(displayText(row.spec.get()));
            setText(null);
            setGraphic(editor);
            editor.requestFocus();
            editor.selectAll();
        }

        @Override
        public void cancelEdit() {
            ShortcutRow row = getTableRow().getItem();
            super.cancelEdit();
            setGraphic(null);
            setText(row == null ? null : displayText(row.spec.get()));
        }

        /**
         * Captures the pressed key combination into the row model (Swing
         * {@code ShortcutSettings.getPanel} capture KeyAdapter): modifier-only presses only
         * update the editor text, every non-modifier key completes the shortcut and commits it.
         * {@code Escape} cancels the edit.
         */
        private void capture(KeyEvent event) {
            if (event.getCode() == KeyCode.ESCAPE) {
                event.consume();
                cancelEdit();
                return;
            }
            KeyCode code = event.getCode();
            if (code == KeyCode.UNDEFINED || KeyStrokeManagerF.isModifier(code)) {
                event.consume();
                return;
            }
            KeyCombination combination = new KeyCodeCombination(code,
                event.isShiftDown() ? ModifierValue.DOWN : ModifierValue.UP,
                event.isControlDown() ? ModifierValue.DOWN : ModifierValue.UP,
                event.isAltDown() ? ModifierValue.DOWN : ModifierValue.UP,
                event.isMetaDown() ? ModifierValue.DOWN : ModifierValue.UP,
                ModifierValue.ANY);
            ShortcutRow row = getTableRow().getItem();
            if (row != null) {
                row.spec.set(KeyStrokeManagerF.toSwingSpec(combination));
            }
            event.consume();
            // the Swing original keeps the editor open for modifier-less keys until it loses
            // the focus; here the value is already committed, so the edit closes right away
            cancelEdit();
        }

        /**
         * @param row the row to check
         * @return the short name of another row with the same non-empty spec, or {@code null}
         */
        private String duplicateOf(ShortcutRow row) {
            String spec = row.spec.get();
            if (spec == null || spec.isEmpty()) {
                return null;
            }
            return tblShortcuts.getItems().stream()
                    .filter(it -> it != row && spec.equals(it.spec.get()))
                    .map(it -> shortName(it.actionId)).findFirst().orElse(null);
        }

        /** @return the spec without the {@code "pressed"} token (Swing display parity) */
        private static String displayText(String spec) {
            return spec == null ? "" : spec.replace("pressed ", "");
        }
    }
}
