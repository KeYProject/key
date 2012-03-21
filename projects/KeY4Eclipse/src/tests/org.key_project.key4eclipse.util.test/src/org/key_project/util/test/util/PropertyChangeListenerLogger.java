package org.key_project.util.test.util;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;
import java.util.List;

/**
 * Implementation of {@link PropertyChangeListener} that logs all caught events.
 * @author Martin Hentschel
 */
public class PropertyChangeListenerLogger implements PropertyChangeListener {
    /**
     * Contains the logged {@link PropertyChangeEvent}s.
     */
    private List<PropertyChangeEvent> log = new LinkedList<PropertyChangeEvent>();

    /**
     * {@inheritDoc}
     */
    @Override
    public void propertyChange(PropertyChangeEvent evt) {
        log.add(evt);
    }
    
    /**
     * Removes the first {@link PropertyChangeEvent} from the log
     * and returns it.
     * @return The first removed {@link PropertyChangeEvent} or {@code null} if no event is logged.
     */
    public PropertyChangeEvent removeFirst() {
        if (!log.isEmpty()) {
            return log.remove(0);
        }
        else {
            return null;
        }
    }
    
    /**
     * Counts the number of {@link PropertyChangeEvent} that are logged.
     * @return The number of logged {@link PropertyChangeEvent}s.
     */
    public int countLog() {
        return log.size();
    }
}
