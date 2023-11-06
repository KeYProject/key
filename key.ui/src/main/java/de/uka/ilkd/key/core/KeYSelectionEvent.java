/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;


/**
 * An event that indicates that the users focused node or proof has changed
 */

public class KeYSelectionEvent {

    /** the source of this event */
    private final KeYSelectionModel source;

    /**
     * creates a new SelectedNodeEvent
     *
     * @param source the SelectedNodeModel where the event had its origin
     */
    public KeYSelectionEvent(KeYSelectionModel source) {
        this.source = source;
    }

    /**
     * returns the KeYSelectionModel that caused this event
     *
     * @return the KeYSelectionModel that caused this event
     */
    public KeYSelectionModel getSource() {
        return source;
    }

}
