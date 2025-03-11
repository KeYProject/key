/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.Properties;

public class LemmaGeneratorSettings extends AbstractSettings {
    public static final String CATEGORY = "LemmaGenerator";
    private static final String SHOW_DIALOG_ADDING_AXIOMS =
        "showDialogWhenAddingAxioms";
    private static final String SHOW_DIALOG_USING_AXIOMS =
        "showDialogWhenUsingTacletsAsAxioms";

    private boolean showDialogAddingAxioms = true;
    private boolean showDialogUsingAxioms = true;

    public boolean isShowingDialogAddingAxioms() {
        return showDialogAddingAxioms;
    }

    public void setShowDialogAddingAxioms(boolean value) {
        var old = this.showDialogAddingAxioms;
        this.showDialogAddingAxioms = value;
        firePropertyChange(SHOW_DIALOG_USING_AXIOMS, old, showDialogUsingAxioms);
    }

    public boolean isShowingDialogUsingAxioms() {
        return showDialogUsingAxioms;
    }

    public void setShowDialogUsingAxioms(boolean value) {
        var old = this.showDialogUsingAxioms;
        this.showDialogUsingAxioms = value;
        firePropertyChange(SHOW_DIALOG_USING_AXIOMS, old, showDialogUsingAxioms);
    }

    @Override
    public void readSettings(Properties props) {
        setShowDialogAddingAxioms(SettingsConverter.read(props,
            "[" + CATEGORY + "]" + SHOW_DIALOG_ADDING_AXIOMS, true));
        setShowDialogUsingAxioms(SettingsConverter.read(props,
            "[" + CATEGORY + "]" + SHOW_DIALOG_USING_AXIOMS, true));
    }

    @Override
    public void writeSettings(Properties props) {
        SettingsConverter.store(props, "[" + CATEGORY + "]" + SHOW_DIALOG_ADDING_AXIOMS,
            showDialogAddingAxioms);
        SettingsConverter.store(props, "[" + CATEGORY + "]" + SHOW_DIALOG_USING_AXIOMS,
            showDialogUsingAxioms);
    }

    @Override
    public void readSettings(Configuration props) {
        var cat = props.getSection(CATEGORY);
        if (cat == null)
            return;
        setShowDialogAddingAxioms(cat.getBool(SHOW_DIALOG_ADDING_AXIOMS, true));
        setShowDialogUsingAxioms(cat.getBool(SHOW_DIALOG_USING_AXIOMS, true));
    }

    @Override
    public void writeSettings(Configuration props) {
        var cat = props.getOrCreateSection(CATEGORY);
        cat.set(SHOW_DIALOG_ADDING_AXIOMS, showDialogAddingAxioms);
        cat.set(SHOW_DIALOG_USING_AXIOMS, showDialogUsingAxioms);
    }
}
