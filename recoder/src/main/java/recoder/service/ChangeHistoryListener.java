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
