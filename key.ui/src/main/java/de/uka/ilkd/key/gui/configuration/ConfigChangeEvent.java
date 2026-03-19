/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.configuration;

/**
 * An event that indicates that the users focused node or proof has changed
 */

public class ConfigChangeEvent {

    /** the source of this event */
    private final Config source;

    /**
     * creates a new ConfigChangeEvent
     *
     * @param source the Config where the event had its origin
     */
    public ConfigChangeEvent(Config source) {
        this.source = source;
    }

    /**
     * returns the Config that caused this event
     *
     * @return the Config that caused this event
     */
    public Config getSource() {
        return source;
    }

}
