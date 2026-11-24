/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Control;
import javafx.scene.control.Spinner;
import javafx.scene.control.TextField;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.EnumProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.IntegerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.StringProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerPropertyVisitor;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerServices;

/**
 * The options of the new SMT translation mechanism (newsmt2), FX port of
 * {@code NewTranslationOptions} (Swing {@code gui/smt/settings/NewTranslationOptions.java}): one
 * control per SMT handler property currently known to {@link SMTHandlerServices} — a combo box
 * for enum properties, a spinner for integer properties, a checkbox for boolean properties and a
 * text field for string properties — read from and written to the proof-dependent
 * {@link NewSMTTranslationSettings} (NewTranslationOptions.java:73-97).
 */
final class NewTranslationOptionsF extends SettingsPanelF implements SettingsProviderF {

    /**
     * One created control together with the SMT handler property it edits (the Swing original
     * stores the property in a client property of the component, NewTranslationOptions.java:58).
     */
    private record PropertyControl(SMTHandlerProperty<?> property, Control control) {
    }

    private final List<PropertyControl> components = new ArrayList<>();

    /**
     * Create a NewTranslationOptionsF object. Note that it uses only the smt properties that are
     * *currently* known to the {@link SMTHandlerServices} instance. Hence, either the creation of
     * this object needs to take place only after the necessary smt properties are known or it
     * needs to be created anew when new smt properties become known.
     */
    NewTranslationOptionsF() {
        setHeaderText(getDescription());
        try {
            for (SMTHandlerProperty<?> property : SMTHandlerServices.getInstance()
                    .getSMTProperties()) {
                components.add(
                    new PropertyControl(property, property.accept(new ComCreationVisitor(), null)));
            }
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }
    }

    @Override
    public String getDescription() {
        return "SMT Translation";
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        NewSMTTranslationSettings newSMTSettings = SettingsManagerF.getNewSmtSettings(window);
        for (PropertyControl component : components) {
            String val = newSMTSettings.get(component.property().getIdentifier());
            if (val != null) {
                setControlValue(component, val);
            }
        }
        return this;
    }

    @Override
    public void apply(MainWindowF window) {
        NewSMTTranslationSettings newSMTSettings = SettingsManagerF.getNewSmtSettings(window);
        for (PropertyControl component : components) {
            String val = controlValue(component);
            if (val != null) {
                newSMTSettings.put(component.property().getIdentifier(), val);
            }
        }
    }

    /**
     * Creates the control of one property (the FX counterpart of the Swing
     * {@code ComCreationVisitor}, NewTranslationOptions.java:99-121).
     */
    private class ComCreationVisitor
            implements SMTHandlerPropertyVisitor<Void, javafx.scene.control.Control> {
        @Override
        public javafx.scene.control.Control visit(EnumProperty<?> eprop, Void unit) {
            return addComboBox(eprop.getLabel(), eprop.getDescription(),
                eprop.getEnumType().getEnumConstants());
        }

        @Override
        public javafx.scene.control.Control visit(IntegerProperty iprop, Void unit) {
            return addIntNumberField(iprop.getLabel(), iprop.getMinimum(), iprop.getMaximum(), 1,
                iprop.getMinimum(), iprop.getDescription(), null);
        }

        @Override
        public javafx.scene.control.Control visit(BooleanProperty bprop, Void unit) {
            return addCheckBox(bprop.getLabel(), bprop.getDescription(), false);
        }

        @Override
        public javafx.scene.control.Control visit(StringProperty sprop, Void unit) {
            return addTextField(sprop.getLabel(), "", sprop.getDescription(), null);
        }
    }

    /**
     * Writes a persisted settings value into the control of its property (the Swing
     * {@code SetVisitor}, NewTranslationOptions.java:123-153; the Swing original casts the
     * integer spinner to a text field, which crashes — the FX port sets the spinner value).
     */
    private static void setControlValue(PropertyControl component, String val) {
        if (component.property() instanceof EnumProperty<?>) {
            if (component.control() instanceof ComboBox<?> rawBox) {
                @SuppressWarnings("unchecked")
                ComboBox<Object> box = (ComboBox<Object>) rawBox;
                for (Object item : box.getItems()) {
                    if (String.valueOf(item).equals(val)) {
                        box.getSelectionModel().select(item);
                        break;
                    }
                }
            }
        } else if (component.property() instanceof IntegerProperty) {
            if (component.control() instanceof Spinner<?> spinner) {
                try {
                    @SuppressWarnings("unchecked")
                    Spinner<Integer> intSpinner = (Spinner<Integer>) spinner;
                    intSpinner.getValueFactory().setValue(Integer.parseInt(val.trim()));
                } catch (NumberFormatException ignored) {
                    // keep the default like the Swing original keeps its spinner state
                }
            }
        } else if (component.property() instanceof BooleanProperty) {
            if (component.control() instanceof CheckBox box) {
                box.setSelected(Boolean.parseBoolean(val));
            }
        } else if (component.property() instanceof StringProperty) {
            if (component.control() instanceof TextField field) {
                field.setText(val);
            }
        }
    }

    /**
     * Reads the current control state as the settings value string (the Swing
     * {@code ApplyVisitor}, NewTranslationOptions.java:155-189).
     */
    private static String controlValue(PropertyControl component) {
        if (component.property() instanceof EnumProperty<?>) {
            if (component.control() instanceof ComboBox<?> rawBox) {
                ComboBox<Object> box = (ComboBox<Object>) rawBox;
                Object item = box.getSelectionModel().getSelectedItem();
                return item != null ? String.valueOf(item) : null;
            }
        } else if (component.property() instanceof IntegerProperty) {
            if (component.control() instanceof Spinner<?> spinner) {
                return String.valueOf(spinner.getValue());
            }
        } else if (component.property() instanceof BooleanProperty) {
            if (component.control() instanceof CheckBox box) {
                return box.isSelected() ? "true" : "false";
            }
        } else if (component.property() instanceof StringProperty) {
            if (component.control() instanceof TextField field) {
                return field.getText();
            }
        }
        return null;
    }
}
