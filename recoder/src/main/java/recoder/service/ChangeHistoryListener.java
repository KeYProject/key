/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

/**
 * Model change listener interface. All change history listeners are informed of changes of the
 * syntactical program model.
 *
 * @author AL
 * @since 0.5
 */
public interface ChangeHistoryListener {
    /**
     * Informs the listener that the syntactical model has changed.
     *
     * @param changes an event containing the changes.
     */
    void modelChanged(ChangeHistoryEvent changes);
}
