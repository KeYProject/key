/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.gui.configuration;

/**
 * The ConfigChangeListener is notified if the UI settings in class Config change.
 */
public interface ConfigChangeListener {

    /** focused node has changed */
    void configChanged(ConfigChangeEvent e);

}
