/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.smt.settings;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.EnumProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.IntegerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.StringProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerPropertyVisitor;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerServices;

import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This is the dialog for the new smt translation mechnism (newsmt2) which aims at a higher degree
 * of flexibility.
 *
 * @author Mattias Ulbrich
 */
@NullMarked
class NewTranslationOptions extends SettingsPanel implements SettingsProvider {

    /**
     * Create a NewTranslationOptions object. Note that it uses only the smt properties that are
     * *currently* known to the SMTHandlerServices instance. Hence, either the creation of this
     * object needs to take place only after the necessary smt properties are known or it needs to
     * be created anew when new smt properties become known.
     *
     * <p>
     * The header and the components are configured while the receiver is still under
     * initialization (EISOP initialization check); they are only rendered after construction
     * completes, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public NewTranslationOptions() {
        setHeaderText(getDescription());
        makeComponents();
    }

    private final List<JComponent> components = new ArrayList<>();

    private void makeComponents() {

        try {
            // This loads only the smt properties that are *currently* known to the
            // SMTHandlerServices instance.
            Collection<SMTHandlerProperty<?>> properties =
                SMTHandlerServices.getInstance().getSMTProperties();
            for (SMTHandlerProperty<?> property : properties) {
                JComponent comp = property.accept(new ComCreationVisitor(), "");
                comp.putClientProperty("smtProperty", property);
                components.add(comp);
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
    public JPanel getPanel(MainWindow window) {
        NewSMTTranslationSettings newSMTSettings = SettingsManager.getNewSmtSettings(window);
        SetVisitor visitor = new SetVisitor();
        for (JComponent component : components) {
            SMTHandlerProperty<?> prop =
                (SMTHandlerProperty<?>) component.getClientProperty("smtProperty");
            if (prop == null) {
                // every component created in makeComponents carries its property
                throw new NullPointerException("No SMT property attached.");
            }
            String id = prop.getIdentifier();
            String val = newSMTSettings.get(id);
            if (val != null) {
                prop.accept(visitor, new Pair<>(val, component));
            }
        }
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        NewSMTTranslationSettings newSMTSettings = SettingsManager.getNewSmtSettings(window);
        ApplyVisitor visitor = new ApplyVisitor(newSMTSettings);
        for (JComponent component : components) {
            SMTHandlerProperty<?> prop =
                (SMTHandlerProperty<?>) component.getClientProperty("smtProperty");
            if (prop == null) {
                // every component created in makeComponents carries its property
                throw new NullPointerException("No SMT property attached.");
            }
            prop.accept(visitor, component);
        }
    }

    private class ComCreationVisitor implements SMTHandlerPropertyVisitor<String, JComponent> {
        @Override
        public JComponent visit(EnumProperty<?> eprop, String unit) {
            Object @Nullable [] constants = eprop.getEnumType().getEnumConstants();
            if (constants == null) {
                // an enum type always exposes its constants
                throw new NullPointerException("No enum constants available.");
            }
            return addComboBox(eprop.getLabel(), eprop.getDescription(), 0, null, constants);
        }

        @Override
        public JComponent visit(IntegerProperty iprop, String unit) {
            return addNumberField(iprop.getLabel(), iprop.getMinimum(), iprop.getMaximum(), 1,
                iprop.getDescription(), emptyValidator());
        }

        @Override
        public JComponent visit(BooleanProperty bprop, String unit) {
            return addCheckBox(bprop.getLabel(), bprop.getDescription(), false, emptyValidator());
        }

        @Override
        public JComponent visit(StringProperty sprop, String unit) {
            return addTextField(sprop.getLabel(), sprop.getDescription(), "", emptyValidator());
        }
    }

    private static class SetVisitor
            implements SMTHandlerPropertyVisitor<Pair<String, JComponent>, String> {

        @Override
        public String visit(EnumProperty<?> enumProp, Pair<String, JComponent> arg) {
            JComboBox<?> box = (JComboBox<?>) arg.second;
            box.setSelectedItem(arg.first);
            return "";
        }

        @Override
        public String visit(IntegerProperty integerProp, Pair<String, JComponent> arg) {
            JTextField field = (JTextField) arg.second;
            field.setText(arg.first);
            return "";
        }

        @Override
        public String visit(BooleanProperty booleanProp, Pair<String, JComponent> arg) {
            JCheckBox box = (JCheckBox) arg.second;
            box.setSelected(Boolean.parseBoolean(arg.first));
            return "";
        }

        @Override
        public String visit(StringProperty stringProp, Pair<String, JComponent> arg) {
            JTextField field = (JTextField) arg.second;
            field.setText(arg.first);
            return "";
        }
    }

    private static class ApplyVisitor implements SMTHandlerPropertyVisitor<JComponent, String> {
        private final NewSMTTranslationSettings settings;

        public ApplyVisitor(NewSMTTranslationSettings newSMTSettings) {
            this.settings = newSMTSettings;
        }

        @Override
        public String visit(EnumProperty<?> enumProp, JComponent arg) {
            Object selectedItem = ((JComboBox<?>) arg).getSelectedItem();
            if (selectedItem == null) {
                // a combo box always has a selected entry when applied
                throw new NullPointerException("No combo box entry selected.");
            }
            String val = selectedItem.toString();
            settings.put(enumProp.getIdentifier(), val);
            return "";
        }

        @Override
        public String visit(IntegerProperty integerProp, JComponent arg) {
            String val = ((JTextField) arg).getText();
            settings.put(integerProp.getIdentifier(), val);
            return "";
        }

        @Override
        public String visit(BooleanProperty booleanProp, JComponent arg) {
            String val = ((JCheckBox) arg).isSelected() ? "true" : "false";
            settings.put(booleanProp.getIdentifier(), val);
            return "";
        }

        @Override
        public String visit(StringProperty stringProp, JComponent arg) {
            String val = ((JTextField) arg).getText();
            settings.put(stringProp.getIdentifier(), val);
            return "";
        }
    }
}
