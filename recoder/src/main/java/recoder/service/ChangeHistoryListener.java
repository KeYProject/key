/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

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
