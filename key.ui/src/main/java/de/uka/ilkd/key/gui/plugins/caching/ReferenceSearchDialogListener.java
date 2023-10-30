/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

/**
 * Interface to receive callbacks from the {@link ReferenceSearchDialog}.
 *
 * @author Arne Keller
 */
public interface ReferenceSearchDialogListener {
    /**
     * Button to close the dialog has been activated.
     *
     * @param dialog the dialog
     */
    void closeButtonClicked(ReferenceSearchDialog dialog);

    /**
     * Button to copy proof steps has been activated.
     *
     * @param dialog the dialog
     */
    void copyButtonClicked(ReferenceSearchDialog dialog);
}
