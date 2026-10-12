/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

/**
 * Listener used to react to user inputs in a {@link ReferenceSearchDialogF}, FX port of
 * {@code ReferenceSearchDialogListener} (Swing ReferenceSearchDialogListener.java:19-27).
 *
 * @author Arne Keller (Swing original)
 * @author WP-4 dialog port (FX)
 */
interface ReferenceSearchDialogListenerF {

    /**
     * The "Apply" button was clicked: copy the relevant proof steps into the current proof
     * (Swing {@code copyButtonClicked}; the default implementation runs the core
     * {@code CopyReferenceResolver} inside the mediator's auto-mode context).
     *
     * @param dialog the dialog that fired the event
     */
    void copyButtonClicked(ReferenceSearchDialogF dialog);

    /**
     * The "Close" button was clicked (Swing {@code closeButtonClicked}: the default
     * implementation disposes the dialog).
     *
     * @param dialog the dialog that fired the event
     */
    void closeButtonClicked(ReferenceSearchDialogF dialog);
}
