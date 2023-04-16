package de.uka.ilkd.key.control.event;

import java.util.EventListener;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;

/**
 * Observes changes on a {@link TermLabelVisibilityManager}.
 *
 * @author Martin Hentschel
 */
public interface TermLabelVisibilityManagerListener extends EventListener {
    /**
     * When the visible term labels have changed.
     *
     * @param e The change event.
     */
    void visibleLabelsChanged(TermLabelVisibilityManagerEvent e);
}
