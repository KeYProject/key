/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.configuration;

import javax.swing.JComponent;


public class ConfigChangeAdapter implements ConfigChangeListener {

    private final JComponent compRef;

    public ConfigChangeAdapter(JComponent comp) {
        assert comp != null;
        compRef = comp;
    }

    public void configChanged(ConfigChangeEvent e) {
        compRef.updateUI();
    }
}
