/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.stream.Collectors;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.ContentDisplay;
import javafx.scene.control.Label;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.paint.Color;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.colors.ColorSettingsF;

/**
 * Settings provider for the configurable colors, counter-part of
 * {@code de.uka.ilkd.key.gui.colors.ColorSettingsProvider} of the Swing module {@code key.ui}.
 * <p>
 * The panel lists the color properties of {@link ColorSettingsF} in a table with the light and
 * the dark color each; both are editable as {@code #AARRGGBB} hex strings (the editor preview
 * colors the text field like the Swing {@code HexColorCellEditor}). Applying transfers the table
 * values into the properties, which persist the overrides into the shared {@code colors.json}
 * and restyle the UI immediately via the CSS property overrides of {@link ColorSettingsF}.
 */
public class ColorSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    private final TableView<ColorSettingsF.ColorPropertyF> tblColors = new TableView<>();
    private boolean initialized;

    public ColorSettingsProviderF() {
        setHeaderText(getDescription());
        setSubHeaderText(
            "Color settings are stored in: " + ColorSettingsF.SETTINGS_FILE.toAbsolutePath());

        TableColumn<ColorSettingsF.ColorPropertyF, String> keyColumn =
            new TableColumn<>("Key");
        keyColumn.setCellValueFactory(
            data -> new javafx.beans.property.SimpleStringProperty(data.getValue().getKey()));
        TableColumn<ColorSettingsF.ColorPropertyF, String> descColumn =
            new TableColumn<>("Description");
        descColumn.setCellValueFactory(data -> new javafx.beans.property.SimpleStringProperty(
            data.getValue().getDescription()));
        TableColumn<ColorSettingsF.ColorPropertyF, Color> lightColumn =
            new TableColumn<>("Light Color");
        lightColumn.setCellValueFactory(data -> data.getValue().lightValueProperty());
        lightColumn.setCellFactory(col -> new ColorCell());
        lightColumn.setOnEditCommit(event -> event.getRowValue()
                .setLightValue(event.getNewValue()));
        TableColumn<ColorSettingsF.ColorPropertyF, Color> darkColumn =
            new TableColumn<>("Dark Color");
        darkColumn.setCellValueFactory(data -> data.getValue().darkValueProperty());
        darkColumn.setCellFactory(col -> new ColorCell());
        darkColumn.setOnEditCommit(event -> event.getRowValue().setDarkValue(event.getNewValue()));
        keyColumn.setPrefWidth(220);
        descColumn.setPrefWidth(200);
        lightColumn.setPrefWidth(130);
        darkColumn.setPrefWidth(130);

        tblColors.getColumns().setAll(keyColumn, descColumn, lightColumn, darkColumn);
        tblColors.setEditable(true);
        // sorted by key ascending, like the Swing TableRowSorter
        tblColors.getSortOrder().add(keyColumn);
        tblColors.setColumnResizePolicy(TableView.CONSTRAINED_RESIZE_POLICY_FLEX_LAST_COLUMN);
        setCenter(tblColors);
    }

    @Override
    public String getDescription() {
        return "Colors";
    }

    @Override
    public Node getPanel(MainWindowF window) {
        if (!initialized) {
            // Swing rebuilds the model on every getPanel; the properties are fixed once defined,
            // so filling the items once is enough
            ObservableList<ColorSettingsF.ColorPropertyF> properties =
                FXCollections.observableList(
                    ColorSettingsF.getInstance().getProperties()
                            .collect(Collectors.toList()));
            tblColors.setItems(properties);
            initialized = true;
        }
        tblColors.sort();
        return this;
    }

    @Override
    public void apply(MainWindowF window) {
        // the property setters already persisted the override and applied the CSS overrides
        ColorSettingsF.getInstance().applyToScenes();
    }

    /**
     * A color cell showing the hex string with a swatch, editable as hex text (Swing's
     * {@code HexColorCellEditor} renders the editor field with the color as background and the
     * inverted color as foreground).
     */
    private static class ColorCell extends TableCell<ColorSettingsF.ColorPropertyF, Color> {

        private final Region swatch = new Region();
        private final TextField editor = new TextField();
        private final HBox box = new HBox(6, swatch, editor);
        private final Region swatchView = new Region();
        private final Label view = new Label();
        private final HBox display = new HBox(6, swatchView, view);

        ColorCell() {
            swatch.setPrefSize(14, 14);
            swatch.getStyleClass().add("color-swatch");
            swatchView.setPrefSize(14, 14);
            swatchView.getStyleClass().add("color-swatch");
            editor.setPrefColumnCount(9);
            HBox.setHgrow(editor, Priority.ALWAYS);
            box.getStyleClass().add("color-editor");
            box.setPadding(new Insets(1));
            editor.setOnAction(e -> commit());
            editor.focusedProperty().addListener((obs, old, focused) -> {
                if (!focused) {
                    cancelEdit();
                }
            });
            setGraphic(null);
            setContentDisplay(ContentDisplay.LEFT);
        }

        @Override
        protected void updateItem(Color item, boolean empty) {
            super.updateItem(item, empty);
            if (empty || item == null) {
                setText(null);
                setGraphic(null);
                return;
            }
            if (isEditing()) {
                editor.setText(ColorSettingsF.toHex(item));
                return;
            }
            show(item);
        }

        @Override
        public void startEdit() {
            super.startEdit();
            Color color = getItem();
            if (color == null) {
                return;
            }
            editor.setText(ColorSettingsF.toHex(color));
            setGraphic(box);
            setText(null);
            styleSwatch(swatch, color);
            editor.requestFocus();
            editor.selectAll();
        }

        @Override
        public void cancelEdit() {
            Color color = getItem();
            super.cancelEdit();
            if (color == null) {
                setGraphic(null);
                return;
            }
            show(color);
        }

        private void show(Color color) {
            view.setText(ColorSettingsF.toHex(color));
            view.setTextFill(readable(color));
            styleSwatch(swatchView, color);
            setGraphic(display);
            setText(null);
        }

        /** Commits the editor content; an unchanged or unparseable value cancels the edit. */
        private void commit() {
            Color color;
            try {
                color = ColorSettingsF.fromHex(editor.getText().trim());
                editor.setStyle("");
            } catch (NumberFormatException e) {
                editor.setStyle("-fx-text-fill: -key-error;");
                return;
            }
            if (color.equals(getItem())) {
                cancelEdit();
                return;
            }
            commitEdit(color);
        }

        private static void styleSwatch(Region region, Color color) {
            region.setStyle("-fx-background-color: " + ColorSettingsF.toCssHex(color)
                + "; -fx-border-color: -key-border; -fx-background-radius: 2;");
        }

        private static javafx.scene.paint.Color readable(Color c) {
            double luminance = 0.299 * c.getRed() + 0.587 * c.getGreen() + 0.114 * c.getBlue();
            return luminance > 0.5 ? Color.BLACK : Color.WHITE;
        }
    }
}
