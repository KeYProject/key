/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;


/**
 * The KeYSelectionListener is notified if the proof or the node the user works with has changed.
 */
public interface KeYSelectionListener {

    /**
     * focused node has changed.
     * <p>
     * Do not modify the list of selection listeners in this callback!
     * </p>
     *
     * @param e event with details about the new selection
     */
    default void selectedNodeChanged(KeYSelectionEvent e) {

    }

    /**
     * the selected proof has changed (e.g. a new proof has been loaded or selected in the UI)
     * <p>
     * Do not modify the list of selection listeners in this callback!
     * </p>
     *
     * @param e event with details about the new selection
     */
    default void selectedProofChanged(KeYSelectionEvent e) {

    }

}
