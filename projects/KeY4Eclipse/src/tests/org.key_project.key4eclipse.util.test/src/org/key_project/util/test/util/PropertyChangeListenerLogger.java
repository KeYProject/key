/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.test.util;

import java.beans.IndexedPropertyChangeEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

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
    
    /**
     * Makes sure that the given {@link PropertyChangeListenerLogger} instances
     * have no event logged.
     * @param loggerWithoutEvent The {@link PropertyChangeListenerLogger} to test.
     */
    public static void assertNoLoggerEvent(PropertyChangeListenerLogger... loggerWithoutEvent) {
        for (PropertyChangeListenerLogger logger : loggerWithoutEvent) {
            TestCase.assertEquals(0, logger.countLog());
        }
    }
    
    /**
     * Makes sure that the given {@link PropertyChangeListenerLogger} instances
     * have logged the defined event.
     * @param expectedSource The expected event source.
     * @param expectedPropertyName The expected property name.
     * @param expectedOldValue The expected old value.
     * @param expectedNewVlaue The expected new value.
     * @param loggerWithEvent The {@link PropertyChangeListenerLogger} to test.
     */
    public static void assertLoggerEvent(Object expectedSource,
                                         String expectedPropertyName,
                                         Object expectedOldValue,
                                         Object expectedNewVlaue,
                                         PropertyChangeListenerLogger... loggerWithEvent) {
        PropertyChangeEvent gloabalEvent = null;
        for (PropertyChangeListenerLogger logger : loggerWithEvent) {
           TestCase.assertEquals(1, logger.countLog());
            PropertyChangeEvent localEvent = logger.removeFirst();
            if (gloabalEvent == null) {
                gloabalEvent = localEvent;
            }
            TestCase.assertSame(gloabalEvent, localEvent);
            assertPropertyChangeEvent(expectedSource, expectedPropertyName, expectedOldValue, expectedNewVlaue, localEvent);
        }
    }
    
    /**
     * Makes sure that the given {@link PropertyChangeEvent} is equal
     * to the defined one.
     * @param expectedSource The expected event source.
     * @param expectedPropertyName The expected property name.
     * @param expectedOldValue The expected old value.
     * @param expectedNewVlaue The expected new value.
     * @param currentEvent The {@link PropertyChangeEvent} to test.
     */
    public static void assertPropertyChangeEvent(Object expectedSource,
                                                 String expectedPropertyName,
                                                 Object expectedOldValue,
                                                 Object expectedNewVlaue,
                                                 PropertyChangeEvent currentEvent) {
        TestCase.assertFalse(currentEvent instanceof IndexedPropertyChangeEvent);
        TestCase.assertEquals(expectedSource, currentEvent.getSource());
        TestCase.assertEquals(expectedPropertyName, currentEvent.getPropertyName());
        TestCase.assertEquals(expectedOldValue, currentEvent.getOldValue());
        TestCase.assertEquals(expectedNewVlaue, currentEvent.getNewValue());
    }
}