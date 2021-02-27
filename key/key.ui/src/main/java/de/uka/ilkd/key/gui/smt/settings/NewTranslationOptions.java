package de.uka.ilkd.key.gui.smt.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.EnumProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.IntegerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.StringProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerServices;

import javax.swing.*;
import java.awt.*;
import java.io.IOException;
import java.util.Collection;

/**
 *
 * This is the dialog for the new smt translation mechnism (newsmt2) which
 * aims at a higher degree of flexibility.
 *
 * @author Mattias Ulbrich
 */
class NewTranslationOptions extends SettingsPanel implements SettingsProvider {

    public NewTranslationOptions() {
        setHeaderText(getDescription());
        makeComponents();
    }

    private void makeComponents() {

        try {
            Collection<SMTHandlerProperty<?>> properties = SMTHandlerServices.getInstance().getSMTProperties();
            for (SMTHandlerProperty<?> property : properties) {
                if (property instanceof BooleanProperty) {
                    BooleanProperty bprop = (BooleanProperty) property;
                    addCheckBox(bprop.getHeading(), bprop.getDescription(),
                            false, emptyValidator());
                }

                if (property instanceof StringProperty) {
                    StringProperty sprop = (StringProperty) property;
                    addTextField(sprop.getHeading(), sprop.getDescription(),
                            "", emptyValidator());
                }

                if (property instanceof IntegerProperty) {
                    IntegerProperty iprop = (IntegerProperty) property;
                    addNumberField(iprop.getHeading(),
                            iprop.getMinimum(), iprop.getMaximum(), 1,
                            iprop.getDescription(),
                            emptyValidator());
                }

                // TODO: Add radio buttons for the enum elements.
//                if (property instanceof EnumProperty) {
//                    EnumProperty<?> eprop = (EnumProperty<?>) property;
//                }
            }
        } catch(IOException ex) {
            throw new RuntimeException(ex);
        }
    }

    @Override
    public String getDescription() {
        return "SMT Translation";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
    }
}
