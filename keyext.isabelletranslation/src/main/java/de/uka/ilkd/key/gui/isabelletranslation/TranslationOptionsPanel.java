/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;

import javax.swing.*;

public class TranslationOptionsPanel extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = -2170118134719823425L;

    public TranslationOptionsPanel() {
        setHeaderText(getDescription());
    }

    @Override
    public String getDescription() {
        return "Translate";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
    }
}
