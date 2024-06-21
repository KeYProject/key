/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;


/**
 * An event that indicates that the users focused node or proof has changed
 */

public class KeYSelectionEvent<Sel> {

    /** the source of this event */
    private final KeYSelectionModel source;

    /** the previously selected item */
    private final Sel previousSelection;

    /**
     * creates a new SelectedNodeEvent
     *
     * @param source
     *        the SelectedNodeModel where the event had its origin
     * @param previousSelection
     *        the previous selected item
     */
    public KeYSelectionEvent(KeYSelectionModel source, Sel previousSelection) {
        this.source = source;
        this.previousSelection = previousSelection;
    }

    /**
     * creates a new SelectedNodeEvent
     *
     * @param source
     *        the SelectedNodeModel where the event had its origin
     */
    public KeYSelectionEvent(KeYSelectionModel source) {
        this(source, null);
    }


    /**
     * returns the KeYSelectionModel that caused this event
     *
     * @return the KeYSelectionModel that caused this event
     */
    public KeYSelectionModel getSource() {
        return source;
    }

    /**
     * returns the previous selected item
     *
     * @return the previous selected item
     */
    public Sel getPreviousSelection() {
        return previousSelection;
    }
}
