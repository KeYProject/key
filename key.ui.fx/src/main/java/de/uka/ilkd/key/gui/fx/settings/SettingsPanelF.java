/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.io.File;
import java.util.List;
import javafx.beans.value.ObservableValue;
import javafx.geometry.HPos;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Control;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Separator;
import javafx.scene.control.Slider;
import javafx.scene.control.Spinner;
import javafx.scene.control.SpinnerValueFactory;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.ColumnConstraints;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;

import de.uka.ilkd.key.gui.fx.colors.ColorSettingsF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF.Key;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A simple panel for using inside the settings dialog, counter-part of
 * {@code SimpleSettingsPanel}/{@code SettingsPanel} of the Swing module {@code key.ui}.
 * <p>
 * The panel provides a header (title and sub title) and a scrollable form area. The Swing
 * originals build the form with MigLayout; here the form is a code-built {@link GridPane} with
 * three columns (title, input, help icon), mirroring the MigLayout {@code wrapAfter(3)} setup.
 * <p>
 * Holds factory methods for creating input components which validate their content while being
 * edited: invalid input marks the component (style class {@code settings-input-error} backed by
 * the {@code SETTINGS_TEXTFIELD_ERROR} color) and shows the error message as a tooltip.
 */
public abstract class SettingsPanelF extends BorderPane {

    private static final Logger LOGGER = LoggerFactory.getLogger(SettingsPanelF.class);

    /**
     * The color property marking erroneous input fields, ported from
     * {@code SimpleSettingsPanel.COLOR_ERROR} (Swing {@code SimpleSettingsPanel}); the value is
     * applied via the {@code settings-input-error} style class using {@code -key-settings-error}.
     */
    public static final ColorSettingsF.ColorPropertyF COLOR_ERROR = ColorSettingsF
            .define("SETTINGS_TEXTFIELD_ERROR", "Color for marking errornous textfields in "
                + "settings dialog", ColorSettingsF.color(200, 100, 100));

    /** the form area; subclasses append rows via the {@code add*} factory methods */
    protected final GridPane pCenter = new GridPane();

    private final Label lblHead = new Label();
    private final Label lblSubhead = new Label();

    protected SettingsPanelF() {
        lblHead.getStyleClass().add("settings-panel-title");
        lblSubhead.getStyleClass().add("settings-panel-subtitle");

        VBox header = new VBox(2, lblHead, lblSubhead, new Separator());
        header.getStyleClass().add("settings-panel-header");
        header.setPadding(new Insets(5, 5, 5, 5));
        setTop(header);

        // three columns like the Swing MigLayout: title (right aligned, no grow), input (grows),
        // help icon (fixed, right)
        ColumnConstraints titles = new ColumnConstraints();
        titles.setHalignment(HPos.RIGHT);
        ColumnConstraints inputs = new ColumnConstraints();
        inputs.setHgrow(Priority.ALWAYS);
        inputs.setFillWidth(true);
        ColumnConstraints helps = new ColumnConstraints();
        helps.setMinWidth(24);
        helps.setPrefWidth(24);
        helps.setHalignment(HPos.RIGHT);
        pCenter.getColumnConstraints().setAll(titles, inputs, helps);
        pCenter.getStyleClass().add("settings-form");
        pCenter.setHgap(8);
        pCenter.setVgap(6);
        pCenter.setPadding(new Insets(8, 8, 8, 8));

        ScrollPane scrollPane = new ScrollPane(pCenter);
        scrollPane.setFitToWidth(true);
        scrollPane.setHbarPolicy(ScrollPane.ScrollBarPolicy.NEVER);
        setCenter(scrollPane);
    }

    /**
     * Sets the header text (the large bold title).
     *
     * @param text the title
     */
    public void setHeaderText(String text) {
        lblHead.setText(text);
    }

    /**
     * Sets the sub header text (the small secondary line below the title).
     *
     * @param text the sub title
     */
    public void setSubHeaderText(String text) {
        lblSubhead.setText(text);
        lblSubhead.setVisible(text != null && !text.isEmpty());
    }

    // ------------------------------------------------------------------
    // error marking (Swing markComponentAsErrornous / demarkComponentAsErrornous)
    // ------------------------------------------------------------------

    /**
     * Marks the given component as erroneous: the error style class is applied and the error
     * message shown as a tooltip (Swing sets the background color from
     * {@code SETTINGS_TEXTFIELD_ERROR}).
     *
     * @param component the input component
     * @param error the error message
     */
    protected void markComponentAsErrornous(Control component, String error) {
        if (!component.getStyleClass().contains("settings-input-error")) {
            component.getStyleClass().add("settings-input-error");
        }
        component.setTooltip(new Tooltip(error));
    }

    /**
     * Removes the error marking of the given component.
     *
     * @param component the input component
     */
    protected void demarkComponentAsErrornous(Control component) {
        component.getStyleClass().remove("settings-input-error");
        component.setTooltip(null);
    }

    /**
     * Validates the value behind the given observable on every change and marks the component
     * accordingly (the port of the Swing {@code DocumentListener}/{@code ChangeListener}
     * adapters).
     *
     * @param component the input component to mark
     * @param observable the value observable
     * @param validator the validator, may be null
     * @param <T> the value type
     */
    protected <T> void wireValidator(Control component, ObservableValue<T> observable,
            Validator<T> validator) {
        if (validator == null) {
            return;
        }
        observable.addListener((obs, old, value) -> {
            try {
                validator.validate(value);
                demarkComponentAsErrornous(component);
            } catch (Exception ex) {
                LOGGER.debug("Rejected settings input: {}", ex.getMessage());
                markComponentAsErrornous(component, ex.getMessage());
            }
        });
    }

    // ------------------------------------------------------------------
    // component factories (ports of the Swing SettingsPanel factory methods)
    // ------------------------------------------------------------------

    /**
     * Creates a labeled separator line (Swing {@code addSeparator}).
     *
     * @param titleText the title shown left of the line
     */
    protected void addSeparator(String titleText) {
        Label label = new Label(titleText);
        label.getStyleClass().add("settings-separator-title");
        Separator separator = new Separator();
        separator.setMinWidth(0);
        HBox.setHgrow(separator, Priority.ALWAYS);
        separator.setMaxWidth(Double.MAX_VALUE);
        HBox box = new HBox(8, label, separator);
        box.setAlignment(Pos.CENTER_LEFT);
        pCenter.add(box, 0, pCenter.getRowCount(), 3, 1);
        GridPane.setHgrow(box, Priority.ALWAYS);
    }

    /**
     * Creates a checkbox row (Swing {@code addCheckBox}); the Swing originals pass an empty
     * validator here, so no validation is wired.
     *
     * @param title the label of the checkbox
     * @param info the help text, may be empty
     * @param value the initial state
     * @return the created checkbox
     */
    protected CheckBox addCheckBox(String title, String info, boolean value) {
        CheckBox checkBox = new CheckBox(title);
        checkBox.setSelected(value);
        addRowWithHelp(info, new Label(), checkBox);
        return checkBox;
    }

    /**
     * Adds a text field row with live validation (Swing {@code addTextField}).
     *
     * @param title the label of the field
     * @param text the initial content
     * @param info the help text, may be empty
     * @param validator the validator, may be null
     * @return the created text field
     */
    protected TextField addTextField(String title, String text, String info,
            Validator<String> validator) {
        TextField field = new TextField(text);
        wireValidator(field, field.textProperty(), validator);
        addTitledComponent(title, field, info);
        return field;
    }

    /**
     * Adds a text area row with live validation (Swing {@code addTextArea}, without the extra
     * scroll pane: the whole panel scrolls here).
     *
     * @param title the label of the area
     * @param text the initial content
     * @param info the help text, may be empty
     * @param validator the validator, may be null
     * @param rows the preferred number of visible rows
     * @return the created text area
     */
    protected TextArea addTextArea(String title, String text, String info,
            Validator<String> validator, int rows) {
        TextArea field = new TextArea(text);
        field.setPrefRowCount(rows);
        field.setWrapText(true);
        wireValidator(field, field.textProperty(), validator);
        addTitledComponent(title, field, info);
        return field;
    }

    /**
     * Adds an integer spinner row for numbers in {@code [min, max]} with live validation (Swing
     * {@code addNumberField}).
     *
     * @param title the label of the field
     * @param min the minimum value
     * @param max the maximum value
     * @param step the step size of the arrow buttons
     * @param value the initial value
     * @param info the help text, may be empty
     * @param validator the validator, may be null
     * @return the created spinner
     */
    protected Spinner<Integer> addIntNumberField(String title, int min, int max, int step,
            int value, String info, Validator<Number> validator) {
        Spinner<Integer> field =
            new Spinner<>(
                new SpinnerValueFactory.IntegerSpinnerValueFactory(min, max, value, step));
        field.setEditable(true);
        wireSpinner(field, validator);
        addTitledComponent(title, field, info);
        return field;
    }

    /**
     * Adds a double spinner row for numbers in {@code [min, max]} with live validation (Swing
     * {@code addNumberField} with a fractional model).
     *
     * @param title the label of the field
     * @param min the minimum value
     * @param max the maximum value
     * @param step the step size of the arrow buttons
     * @param value the initial value
     * @param info the help text, may be empty
     * @param validator the validator, may be null
     * @return the created spinner
     */
    protected Spinner<Double> addDoubleNumberField(String title, double min, double max,
            double step, double value, String info, Validator<Number> validator) {
        Spinner<Double> field =
            new Spinner<>(
                new SpinnerValueFactory.DoubleSpinnerValueFactory(min, max, value, step));
        field.setEditable(true);
        wireSpinner(field, validator);
        addTitledComponent(title, field, info);
        return field;
    }

    private void wireSpinner(Spinner<? extends Number> field, Validator<Number> validator) {
        if (validator == null) {
            return;
        }
        field.valueProperty().addListener((obs, old, value) -> {
            try {
                validator.validate(value);
                demarkComponentAsErrornous(field);
            } catch (Exception ex) {
                LOGGER.debug("Rejected settings input: {}", ex.getMessage());
                markComponentAsErrornous(field, ex.getMessage());
            }
        });
    }

    /**
     * Adds a combo box row (Swing {@code addComboBox}).
     *
     * @param <T> the item type
     * @param title the label of the combo box, may be null to skip the title
     * @param info the help text, may be empty
     * @param items the items
     * @return the created combo box
     */
    @SafeVarargs
    protected final <T> ComboBox<T> addComboBox(String title, String info, T... items) {
        ComboBox<T> comboBox = new ComboBox<>();
        comboBox.getItems().setAll(items);
        addTitledComponent(title, comboBox, info);
        return comboBox;
    }

    /**
     * Creates a combo box with live validation without adding a row (Swing
     * {@code createSelection}).
     *
     * @param <T> the item type
     * @param items the items
     * @param validator the validator, may be null
     * @return the created combo box
     */
    @SafeVarargs
    protected final <T> ComboBox<T> createSelection(Validator<T> validator, T... items) {
        ComboBox<T> comboBox = new ComboBox<>();
        comboBox.getItems().setAll(items);
        wireValidator(comboBox, comboBox.getSelectionModel().selectedItemProperty(), validator);
        return comboBox;
    }

    /**
     * Adds a titled component row: a right-aligned title, the component and the help icon (Swing
     * {@code addTitledComponent}).
     *
     * @param title the label of the component, may be null to skip the title
     * @param component the input component
     * @param helpText the help text, may be empty
     */
    protected void addTitledComponent(String title, Node component, String helpText) {
        Node titleNode = title == null ? new Label() : new Label(title);
        addRowWithHelp(helpText, titleNode, component);
    }

    /**
     * Adds a row of components followed by the help icon column (Swing
     * {@code addRowWithHelp}): the first component goes into the title column, the remaining
     * components share the input column.
     *
     * @param info the help text; empty text leaves an empty help cell
     * @param components the components of the row
     */
    protected void addRowWithHelp(String info, Node... components) {
        int row = pCenter.getRowCount();
        Node title = components.length > 0 ? components[0] : new Label();
        pCenter.add(title, 0, row);
        Node input;
        if (components.length == 2) {
            input = components[1];
        } else if (components.length > 2) {
            HBox box = new HBox(8, java.util.Arrays.copyOfRange(components, 1, components.length));
            box.setAlignment(Pos.CENTER_LEFT);
            input = box;
        } else {
            input = new Label();
        }
        pCenter.add(input, 1, row);
        if (info != null && !info.isEmpty()) {
            pCenter.add(createHelpLabel(info), 2, row);
        } else {
            pCenter.add(new Label(), 2, row);
        }
    }

    /**
     * Adds a file chooser row: a text field with a browse button (Swing
     * {@code addFileChooserPanel}; the Swing original uses {@code KeYFileChooser}, here a plain
     * JavaFX {@link FileChooser}).
     *
     * @param title the label of the field
     * @param file the initial file name
     * @param info the help text, may be empty
     * @param isSave whether the chooser opens in save mode
     * @param validator the validator, may be null
     * @return the created text field
     */
    protected TextField addFileChooserPanel(String title, String file, String info,
            boolean isSave, Validator<String> validator) {
        TextField textField = new TextField(file);
        wireValidator(textField, textField.textProperty(), validator);
        javafx.scene.control.Button btnFileChooser =
            new javafx.scene.control.Button(null, IconFactoryF.createIcon(Key.SEARCH, 12));
        btnFileChooser.setOnAction(e -> {
            FileChooser chooser =
                new FileChooser();
            chooser.setTitle(isSave ? "Save file" : "Open file");
            chooser.getExtensionFilters().add(new FileChooser.ExtensionFilter("All Files", "*.*"));
            File initial = new File(textField.getText());
            if (isSave) {
                if (!initial.isDirectory() && initial.getParentFile() != null) {
                    chooser.setInitialDirectory(initial.getParentFile());
                }
                chooser.setInitialFileName(initial.getName());
            } else if (initial.isDirectory()) {
                chooser.setInitialDirectory(initial);
            }
            File selected =
                isSave ? chooser.showSaveDialog(btnFileChooser.getScene().getWindow())
                        : chooser.showOpenDialog(btnFileChooser.getScene().getWindow());
            if (selected != null) {
                textField.setText(selected.getAbsolutePath());
            }
        });
        HBox box = new HBox(4, textField, btnFileChooser);
        HBox.setHgrow(textField, Priority.ALWAYS);
        addTitledComponent(title, box, info);
        return textField;
    }

    /**
     * Adds a group of radio buttons as one row (Swing {@code addRadioButtons}).
     *
     * @param title the label of the group
     * @param alternatives the alternatives, rendered via {@code toString}
     * @param description the help text, may be empty
     * @return the toggle group selecting the alternatives
     */
    protected javafx.scene.control.ToggleGroup addRadioButtons(String title,
            List<?> alternatives, String description) {
        VBox items = new VBox(2);
        javafx.scene.control.ToggleGroup group = new javafx.scene.control.ToggleGroup();
        for (Object alt : alternatives) {
            javafx.scene.control.RadioButton button =
                new javafx.scene.control.RadioButton(alt.toString());
            button.setToggleGroup(group);
            button.setUserData(alt);
            items.getChildren().add(button);
        }
        addTitledComponent(title, items, description);
        return group;
    }

    /**
     * Creates a help label showing the given information as a tooltip (Swing
     * {@code createHelpLabel}).
     *
     * @param s the information
     * @return a label with a question mark icon and the tooltip
     */
    public static Label createHelpLabel(String s) {
        Label infoLabel = new Label(null, IconFactoryF.createIcon(Key.HELP));
        if (s != null && !s.isEmpty()) {
            infoLabel.setTooltip(new Tooltip(s));
        }
        return infoLabel;
    }

    /**
     * Creates an empty validator instance (Swing {@code emptyValidator}).
     *
     * @param <T> arbitrary
     * @return a validator accepting everything
     */
    protected static <T> Validator<T> emptyValidator() {
        return value -> {
        };
    }

    /**
     * Adds a slider row (not present in the Swing original; helper for range inputs that would
     * otherwise need a spinner).
     *
     * @param title the label of the slider
     * @param min the minimum value
     * @param max the maximum value
     * @param value the initial value
     * @param info the help text, may be empty
     * @return the created slider
     */
    protected Slider addSlider(String title, double min, double max, double value, String info) {
        Slider slider = new Slider(min, max, value);
        slider.setShowTickLabels(true);
        addTitledComponent(title, slider, info);
        return slider;
    }

    /**
     * A filler region for grid rows without content in the first column.
     *
     * @return an empty region
     */
    protected static Region spacer() {
        return new Region();
    }
}
