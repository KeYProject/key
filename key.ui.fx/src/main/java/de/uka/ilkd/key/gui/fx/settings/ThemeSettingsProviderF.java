/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.collections.FXCollections;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.ToggleGroup;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * Settings provider for the look of the JavaFX UI: light/dark theme and the base font size. The
 * font size is persisted within the core {@link ViewSettings} (same {@code SIZES} as the Swing
 * module's {@code Config}); the theme is managed by the {@link ThemeManager}.
 */
public final class ThemeSettingsProviderF implements SettingsProviderF {

    private final ToggleGroup themeGroup = new ToggleGroup();
    private final ComboBox<Integer> fontSizeComboBox = new ComboBox<>();

    private RadioButton lightRadio;
    private RadioButton darkRadio;

    @Override
    public String getDescription() {
        return "Look & Feel";
    }

    @Override
    public String getCategory() {
        return "General";
    }

    @Override
    public Node getPanel() {
        lightRadio = createRadio("Light", Theme.LIGHT);
        darkRadio = createRadio("Dark", Theme.DARK);
        Theme current = ThemeManager.getInstance().getTheme();
        (current == Theme.DARK ? darkRadio : lightRadio).setSelected(true);

        fontSizeComboBox.setItems(
            FXCollections.observableArrayList(ConfigF.SIZES[0], ConfigF.SIZES[1], ConfigF.SIZES[2],
                ConfigF.SIZES[3], ConfigF.SIZES[4], ConfigF.SIZES[5]));
        fontSizeComboBox.getSelectionModel().select(ConfigF.DEFAULT.sizeIndex());

        VBox packet = new VBox(16);
        packet.setPadding(new Insets(12));

        GridPane themeRow = new GridPane();
        themeRow.setHgap(8);
        themeRow.add(new Label("Theme:"), 0, 0);
        themeRow.add(lightRadio, 1, 0);
        themeRow.add(darkRadio, 2, 0);

        GridPane fontRow = new GridPane();
        fontRow.setHgap(8);
        fontRow.add(new Label("Base font size:"), 0, 0);
        fontRow.add(fontSizeComboBox, 1, 0);

        packet.getChildren().addAll(themeRow, fontRow);
        return packet;
    }

    @Override
    public void apply() {
        Theme selected = darkRadio.isSelected() ? Theme.DARK : Theme.LIGHT;
        ThemeManager.getInstance().setTheme(selected);
        int index = fontSizeComboBox.getSelectionModel().getSelectedIndex();
        if (index >= 0) {
            ViewSettings viewSettings =
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
            viewSettings.setFontIndex(index);
        }
    }

    @Override
    public void reset() {
        Theme current = ThemeManager.getInstance().getTheme();
        (current == Theme.DARK ? darkRadio : lightRadio).setSelected(true);
        fontSizeComboBox.getSelectionModel().select(ConfigF.DEFAULT.sizeIndex());
    }

    private RadioButton createRadio(String label, Theme theme) {
        RadioButton radio = new RadioButton(label);
        radio.setToggleGroup(themeGroup);
        radio.setUserData(theme);
        return radio;
    }
}
