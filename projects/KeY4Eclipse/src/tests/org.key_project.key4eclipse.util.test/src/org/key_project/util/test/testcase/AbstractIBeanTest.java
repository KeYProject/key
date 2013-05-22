/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.util.test.testcase;

import java.beans.IndexedPropertyChangeEvent;
import java.beans.PropertyChangeEvent;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.bean.Bean;
import org.key_project.util.bean.IBean;
import org.key_project.util.test.util.PropertyChangeListenerLogger;

/**
 * Provides the basic funcationality to test an {@link IBean} implementation.
 * @author Martin Hentschel
 * @see BeanTest
 * @see AbstractBeanViewPartTest
 */
public abstract class AbstractIBeanTest extends TestCase {
    /**
     * Creates the {@link ITestBean} to test.
     * @return
     */
    protected abstract ITestBean createTestBean();
    
    /**
     * Defines the required methods of an {@link IBean} which is tested.
     * @author Martin Hentschel
     */
    protected static interface ITestBean extends IBean {
       /**
        * Java Bean property for {@link #objectValue}.
        */
       public static final String PROP_OBJECT_VALUE = "objectValue";

       /**
        * Java Bean property for {@link #intValue}.
        */
       public static final String PROP_INT_VALUE = "intValue";

       /**
        * Java Bean property for {@link #booleanValue}.
        */
       public static final String PROP_BOOLEAN_VALUE = "booleanValue";

       /**
        * Java Bean property for {@link #objectArray}.
        */
       public static final String PROP_OBJECT_ARRAY = "objectArray";

       /**
        * Java Bean property for {@link #intArray}.
        */
       public static final String PROP_INT_ARRAY = "intArray";

       /**
        * Java Bean property for {@link #booleanArray}.
        */
       public static final String PROP_BOOLEAN_ARRAY = "booleanArray";
       
       /**
        * Returns the object value.
        * @return The object value.
        */
       public Object getObjectValue();

       /**
        * Sets the object value.
        * @param objectValue The object value to set.
        */
       public void setObjectValue(Object objectValue);

       /**
        * Returns the int value.
        * @return The int value.
        */
       public int getIntValue();

       /**
        * Sets the int value.
        * @param intValue The int value to set.
        */
       public void setIntValue(int intValue);

       /**
        * Returns the boolean value.
        * @return The boolean value.
        */
       public boolean isBooleanValue();

       /**
        * Sets the boolean value.
        * @param booleanValue The boolean value to set.
        */
       public void setBooleanValue(boolean booleanValue);

       /**
        * Returns the object value at the given index.
        * @param index The array index.
        * @return The object value.
        */
       public Object getObjectArray(int index);

       /**
        * Sets the object value at the given index.
        * @param index The array index.
        * @param objectValue The value to set.
        */
       public void setObjectArray(int index, Object objectValue);

       /**
        * Returns the int value at the given index.
        * @param index The array index.
        * @return The int value.
        */
       public int getIntArray(int index);

       /**
        * Sets the int value at the given index.
        * @param index The array index.
        * @param intValue The value to set.
        */
       public void setIntArray(int index, int intValue);

       /**
        * Returns the boolean value at the given index.
        * @param index The array index.
        * @return The boolean value.
        */
       public boolean getBooleanArray(int index);

       /**
        * Sets the boolean value at the given index.
        * @param index The array index.
        * @param booleanValue The boolean value to set.
        */
       public void setBooleanArray(int index, boolean booleanValue);
       
       /**
        * Fires an invalid event.
        */
       public void fireInvalidEvent();
    }
   
    /**
     * Tests {@link Bean#firePropertyChange(PropertyChangeEvent)}
     */
    @Test
    public void testFirePropertyChange_PropertyChangeEvent() {
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger general2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger obj1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger obj2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger booleanObj1 = new PropertyChangeListenerLogger();
        ITestBean bean = createTestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_VALUE, obj1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_VALUE, obj2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, booleanObj1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_VALUE, booleanObj1);
        // Fire invalid event
        bean.fireInvalidEvent();
        PropertyChangeListenerLogger.assertLoggerEvent(bean, "INVALID", "INVALID_OLD", "INVALID_NEW", general1, general2);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, obj1, obj2, booleanObj1);
    }
    
    /**
     * Tests {@link Bean#fireIndexedPropertyChange(String, int, Object, Object)}
     */
    @Test
    public void testFireIndexedPropertyChange_Object() {
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger general2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger obj1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger obj2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger booleanObj1 = new PropertyChangeListenerLogger();
        ITestBean bean = createTestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, boolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_ARRAY, obj1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_ARRAY, obj2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, booleanObj1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_ARRAY, booleanObj1);
        // Test event from null to "A"
        bean.setObjectArray(1, "A");
        assertIndexLoggerEvent(bean, ITestBean.PROP_OBJECT_ARRAY, 1, null, "A", general1, general2, obj1, obj2, booleanObj1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from "A" to "A"
        bean.setObjectArray(1, "A");
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Test event from "A" to "B"
        bean.setObjectArray(1, "B");
        assertIndexLoggerEvent(bean, ITestBean.PROP_OBJECT_ARRAY, 1, "A", "B", general1, general2, obj1, obj2, booleanObj1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from "B" to "B"
        bean.setObjectArray(1, "B");
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(ITestBean.PROP_OBJECT_ARRAY, obj1);
        // Test event from "B" to "C"
        bean.setObjectArray(1, "C");
        assertIndexLoggerEvent(bean, ITestBean.PROP_OBJECT_ARRAY, 1, "B", "C", general2, obj2, booleanObj1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, obj1);
    }
    
    /**
     * Tests {@link Bean#fireIndexedPropertyChange(String, int, int, int)}
     */
    @Test
    public void testFireIndexedPropertyChange_int() {
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger general2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger int1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger int2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger booleanInt1 = new PropertyChangeListenerLogger();
        ITestBean bean = createTestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, boolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_ARRAY, int1);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_ARRAY, int2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, booleanInt1);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_ARRAY, booleanInt1);
        // Test event from 0 to 2
        bean.setIntArray(0, 2);
        assertIndexLoggerEvent(bean, ITestBean.PROP_INT_ARRAY, 0, 0, 2, general1, general2, int1, int2, booleanInt1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from 2 to 2
        bean.setIntArray(0, 2);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Test event from 2 to -1
        bean.setIntArray(0, -1);
        assertIndexLoggerEvent(bean, ITestBean.PROP_INT_ARRAY, 0, 2, -1, general1, general2, int1, int2, booleanInt1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from -1 to -1
        bean.setIntArray(0, -1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(ITestBean.PROP_INT_ARRAY, int1);
        // Test event from -1 to 3
        bean.setIntArray(0, 3);
        assertIndexLoggerEvent(bean, ITestBean.PROP_INT_ARRAY, 0, -1, 3, general2, int2, booleanInt1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, int1);
    }
    
    /**
     * Tests {@link Bean#fireIndexedPropertyChange(String, int, boolean, boolean)}
     */
    @Test
    public void testFireIndexedPropertyChange_boolean() {
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger general2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger int1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger intBoolean1 = new PropertyChangeListenerLogger();
        ITestBean bean = createTestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_ARRAY, int1);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, boolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, boolean2);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_ARRAY, intBoolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, intBoolean1);
        // Test event from false to true
        bean.setBooleanArray(0, true);
        assertIndexLoggerEvent(bean, ITestBean.PROP_BOOLEAN_ARRAY, 0, false, true, general1, general2, boolean1, boolean2, intBoolean1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1);
        // Test no event from true to true
        bean.setBooleanArray(0, true);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Test event from true to false
        bean.setBooleanArray(0, false);
        assertIndexLoggerEvent(bean, ITestBean.PROP_BOOLEAN_ARRAY, 0, true, false, general1, general2, boolean1, boolean2, intBoolean1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1);
        // Test no event from false to false
        bean.setBooleanArray(0, false);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(ITestBean.PROP_BOOLEAN_ARRAY, boolean1);
        // Test event from false to true again with less listeners
        bean.setBooleanArray(0, true);
        assertIndexLoggerEvent(bean, ITestBean.PROP_BOOLEAN_ARRAY, 0, false, true, general2, boolean2, intBoolean1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1, general1, boolean1);
    }
    
    /**
     * Makes sure that the given {@link PropertyChangeListenerLogger} instances
     * have logged the defined event.
     * @param expectedSource The expected event source.
     * @param expectedPropertyName The expected property name.
     * @param expectedIndex The expected index.
     * @param expectedOldValue The expected old value.
     * @param expectedNewVlaue The expected new value.
     * @param loggerWithEvent The {@link PropertyChangeListenerLogger} to test.
     */
    protected void assertIndexLoggerEvent(Object expectedSource,
                                          String expectedPropertyName,
                                          int expectedIndex,
                                          Object expectedOldValue,
                                          Object expectedNewVlaue,
                                          PropertyChangeListenerLogger... loggerWithEvent) {
        PropertyChangeEvent gloabalEvent = null;
        for (PropertyChangeListenerLogger logger : loggerWithEvent) {
            assertEquals(1, logger.countLog());
            PropertyChangeEvent localEvent = logger.removeFirst();
            if (gloabalEvent == null) {
                gloabalEvent = localEvent;
            }
            assertSame(gloabalEvent, localEvent);
            assertIndexPropertyChangeEvent(expectedSource, expectedPropertyName, expectedIndex, expectedOldValue, expectedNewVlaue, localEvent);
        }
    }
    
    /**
     * Makes sure that the given {@link PropertyChangeEvent} is equal
     * to the defined one.
     * @param expectedSource The expected event source.
     * @param expectedPropertyName The expected property name.
     * @param expectedIndex The expected index.
     * @param expectedOldValue The expected old value.
     * @param expectedNewVlaue The expected new value.
     * @param currentEvent The {@link PropertyChangeEvent} to test.
     */
    protected void assertIndexPropertyChangeEvent(Object expectedSource,
                                                  String expectedPropertyName,
                                                  int expectedIndex,
                                                  Object expectedOldValue,
                                                  Object expectedNewVlaue,
                                                  PropertyChangeEvent currentEvent) {
        assertTrue(currentEvent instanceof IndexedPropertyChangeEvent);
        IndexedPropertyChangeEvent iCurrentEvent = (IndexedPropertyChangeEvent)currentEvent;
        assertEquals(expectedSource, currentEvent.getSource());
        assertEquals(expectedPropertyName, currentEvent.getPropertyName());
        assertEquals(expectedIndex, iCurrentEvent.getIndex());
        assertEquals(expectedOldValue, currentEvent.getOldValue());
        assertEquals(expectedNewVlaue, currentEvent.getNewValue());
    }
    
    /**
     * Tests {@link Bean#firePropertyChange(String, Object, Object)}
     */
    @Test
    public void testFirePropertyChange_Object() {
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger general2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger obj1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger obj2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger booleanObj1 = new PropertyChangeListenerLogger();
        ITestBean bean = createTestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_VALUE, obj1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_VALUE, obj2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, booleanObj1);
        bean.addPropertyChangeListener(ITestBean.PROP_OBJECT_VALUE, booleanObj1);
        // Test event from null to "A"
        bean.setObjectValue("A");
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_OBJECT_VALUE, null, "A", general1, general2, obj1, obj2, booleanObj1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from "A" to "A"
        bean.setObjectValue("A");
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Test event from "A" to "B"
        bean.setObjectValue("B");
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_OBJECT_VALUE, "A", "B", general1, general2, obj1, obj2, booleanObj1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from "B" to "B"
        bean.setObjectValue("B");
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(ITestBean.PROP_OBJECT_VALUE, obj1);
        // Test event from "B" to "C"
        bean.setObjectValue("C");
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_OBJECT_VALUE, "B", "C", general2, obj2, booleanObj1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, obj1);
    }
    
    /**
     * Tests {@link Bean#firePropertyChange(String, int, int)}
     */
    @Test
    public void testFirePropertyChange_int() {
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger general2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger int1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger int2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger booleanInt1 = new PropertyChangeListenerLogger();
        ITestBean bean = createTestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_VALUE, int1);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_VALUE, int2);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, booleanInt1);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_VALUE, booleanInt1);
        // Test event from 0 to 2
        bean.setIntValue(2);
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_INT_VALUE, 0, 2, general1, general2, int1, int2, booleanInt1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from 2 to 2
        bean.setIntValue(2);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Test event from 2 to -1
        bean.setIntValue(-1);
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_INT_VALUE, 2, -1, general1, general2, int1, int2, booleanInt1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1);
        // Test no event from -1 to -1
        bean.setIntValue(-1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(ITestBean.PROP_INT_VALUE, int1);
        // Test event from -1 to 3
        bean.setIntValue(3);
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_INT_VALUE, -1, 3, general2, int2, booleanInt1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(boolean1, general1, int1);
    }
    
    /**
     * Tests {@link Bean#firePropertyChange(String, boolean, boolean)}
     */
    @Test
    public void testFirePropertyChange_boolean() {
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger general2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger int1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger boolean2 = new PropertyChangeListenerLogger();
        PropertyChangeListenerLogger intBoolean1 = new PropertyChangeListenerLogger();
        ITestBean bean = createTestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_VALUE, int1);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean2);
        bean.addPropertyChangeListener(ITestBean.PROP_INT_VALUE, intBoolean1);
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, intBoolean1);
        // Test event from false to true
        bean.setBooleanValue(true);
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_BOOLEAN_VALUE, false, true, general1, general2, boolean1, boolean2, intBoolean1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1);
        // Test no event from true to true
        bean.setBooleanValue(true);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Test event from true to false
        bean.setBooleanValue(false);
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_BOOLEAN_VALUE, true, false, general1, general2, boolean1, boolean2, intBoolean1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1);
        // Test no event from false to false
        bean.setBooleanValue(false);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1);
        // Test event from false to true again with less listeners
        bean.setBooleanValue(true);
        PropertyChangeListenerLogger.assertLoggerEvent(bean, ITestBean.PROP_BOOLEAN_VALUE, false, true, general2, boolean2, intBoolean1);
        PropertyChangeListenerLogger.assertNoLoggerEvent(int1, general1, boolean1);
    }
    
    /**
     * Tests for:
     * <ul>
     *    <li>{@link IBean#addPropertyChangeListener(java.beans.PropertyChangeListener)}</li>
     *    <li>{@link IBean#addPropertyChangeListener(String, java.beans.PropertyChangeListener)}</li>
     *    <li>{@link IBean#getPropertyChangeListeners()}</li>
     *    <li>{@link IBean#getPropertyChangeListeners(String)}</li>
     *    <li>{@link IBean#hasListener(java.beans.PropertyChangeListener)}</li>
     *    <li>{@link IBean#hasListener(String, java.beans.PropertyChangeListener)}</li>
     *    <li>{@link IBean#hasListeners()}</li>
     *    <li>{@link IBean#hasListeners(String)}</li>
     * </ul>
     */
    @Test
    public void testListenerManagement() {
        // Test bean without listeners
       ITestBean bean = createTestBean();
        assertEquals(0, bean.getPropertyChangeListeners().length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertFalse(bean.hasListeners());
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_INT_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListeners(ITestBean.PROP_INT_ARRAY));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        // Add general listener
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        bean.addPropertyChangeListener(general1);
        assertEquals(1, bean.getPropertyChangeListeners().length);
        assertEquals(general1, bean.getPropertyChangeListeners()[0]);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertTrue(bean.hasListeners());
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(ITestBean.PROP_INT_VALUE));
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListeners(ITestBean.PROP_INT_ARRAY));
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListener(general1));
        // Add boolean listener
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        bean.addPropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1);
        assertEquals(2, bean.getPropertyChangeListeners().length);
        assertEquals(general1, bean.getPropertyChangeListeners()[0]);
        assertEquals(1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_VALUE).length);
        assertEquals(1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertTrue(bean.hasListeners());
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(ITestBean.PROP_INT_VALUE));
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListeners(ITestBean.PROP_INT_ARRAY));
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListener(general1));
        assertFalse(bean.hasListener(ITestBean.PROP_BOOLEAN_VALUE, general1));
        assertFalse(bean.hasListener(boolean1));
        assertTrue(bean.hasListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1));
        assertFalse(bean.hasListener(ITestBean.PROP_INT_VALUE, boolean1));
        // Remove general listener
        bean.removePropertyChangeListener(general1);
        assertEquals(1, bean.getPropertyChangeListeners().length);
        assertEquals(1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_VALUE).length);
        assertEquals(1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertTrue(bean.hasListeners());
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_INT_VALUE));
        assertTrue(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListeners(ITestBean.PROP_INT_ARRAY));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListener(general1));
        assertFalse(bean.hasListener(ITestBean.PROP_BOOLEAN_VALUE, general1));
        assertFalse(bean.hasListener(boolean1));
        assertTrue(bean.hasListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1));
        assertFalse(bean.hasListener(ITestBean.PROP_INT_VALUE, boolean1));
        // Remove boolean listener
        bean.removePropertyChangeListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1);
        assertEquals(0, bean.getPropertyChangeListeners().length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(ITestBean.PROP_BOOLEAN_ARRAY).length);
        assertFalse(bean.hasListeners());
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_INT_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListeners(ITestBean.PROP_INT_ARRAY));
        assertFalse(bean.hasListeners(ITestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListener(general1));
        assertFalse(bean.hasListener(ITestBean.PROP_BOOLEAN_VALUE, general1));
        assertFalse(bean.hasListener(boolean1));
        assertFalse(bean.hasListener(ITestBean.PROP_BOOLEAN_VALUE, boolean1));
        assertFalse(bean.hasListener(ITestBean.PROP_INT_VALUE, boolean1));
    }
}