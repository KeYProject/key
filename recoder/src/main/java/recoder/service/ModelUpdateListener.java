/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.EventObject;

/**
 * Model change listener interface. All change history listeners are informed of changes of the
 * syntactical program model.
 *
 * @author AL
 * @since 0.5
 */
public interface ModelUpdateListener {

    /**
     * Informs the listener that the meta model is now being updated.
     *
     * @param event an event object containing the change history service as source.
     * @since 0.72
     */
    void modelUpdating(EventObject event);

    /**
     * Informs the listener that the meta model has been updated.
     *
     * @param event an event object containing the change history service as source.
     */
    void modelUpdated(EventObject event);
}
