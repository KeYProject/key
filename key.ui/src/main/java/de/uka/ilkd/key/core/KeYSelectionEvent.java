/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;


/**
 * An event that indicates that the users focused node or proof has changed
 *
 * @param source the source of this event
 * @param previousSelection the previously selected item
 * @param currentSelection the previously selected item
 */
public record KeYSelectionEvent<Sel>(
        KeYSelectionModel source, Sel previousSelection, Sel currentSelection) {
    /**
     * returns the KeYSelectionModel that caused this event
     *
     * @return the KeYSelectionModel that caused this event
     */
    @Override
    public KeYSelectionModel source() {
        return source;
    }
}
