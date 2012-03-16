package org.key_project.util.test.testcase;

import java.beans.IndexedPropertyChangeEvent;
import java.beans.PropertyChangeEvent;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.bean.Bean;
import org.key_project.util.bean.IBean;
import org.key_project.util.test.util.PropertyChangeListenerLogger;

/**
 * Tests for {@link Bean}.
 * @author Martin Hentschel
 */
public class BeanTest extends TestCase {
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
        TestBean bean = new TestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_VALUE, obj1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_VALUE, obj2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, booleanObj1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_VALUE, booleanObj1);
        // Fire invalid event
        bean.fireInvalidEvent();
        assertLoggerEvent(bean, "INVALID", "INVALID_OLD", "INVALID_NEW", general1, general2);
        assertNoLoggerEvent(boolean1, obj1, obj2, booleanObj1);
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
        TestBean bean = new TestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, boolean1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_ARRAY, obj1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_ARRAY, obj2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, booleanObj1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_ARRAY, booleanObj1);
        // Test event from null to "A"
        bean.setObjectArray(1, "A");
        assertIndexLoggerEvent(bean, TestBean.PROP_OBJECT_ARRAY, 1, null, "A", general1, general2, obj1, obj2, booleanObj1);
        assertNoLoggerEvent(boolean1);
        // Test no event from "A" to "A"
        bean.setObjectArray(1, "A");
        assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Test event from "A" to "B"
        bean.setObjectArray(1, "B");
        assertIndexLoggerEvent(bean, TestBean.PROP_OBJECT_ARRAY, 1, "A", "B", general1, general2, obj1, obj2, booleanObj1);
        assertNoLoggerEvent(boolean1);
        // Test no event from "B" to "B"
        bean.setObjectArray(1, "B");
        assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(TestBean.PROP_OBJECT_ARRAY, obj1);
        // Test event from "B" to "C"
        bean.setObjectArray(1, "C");
        assertIndexLoggerEvent(bean, TestBean.PROP_OBJECT_ARRAY, 1, "B", "C", general2, obj2, booleanObj1);
        assertNoLoggerEvent(boolean1, general1, obj1);
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
        TestBean bean = new TestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, boolean1);
        bean.addPropertyChangeListener(TestBean.PROP_INT_ARRAY, int1);
        bean.addPropertyChangeListener(TestBean.PROP_INT_ARRAY, int2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, booleanInt1);
        bean.addPropertyChangeListener(TestBean.PROP_INT_ARRAY, booleanInt1);
        // Test event from 0 to 2
        bean.setIntArray(0, 2);
        assertIndexLoggerEvent(bean, TestBean.PROP_INT_ARRAY, 0, 0, 2, general1, general2, int1, int2, booleanInt1);
        assertNoLoggerEvent(boolean1);
        // Test no event from 2 to 2
        bean.setIntArray(0, 2);
        assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Test event from 2 to -1
        bean.setIntArray(0, -1);
        assertIndexLoggerEvent(bean, TestBean.PROP_INT_ARRAY, 0, 2, -1, general1, general2, int1, int2, booleanInt1);
        assertNoLoggerEvent(boolean1);
        // Test no event from -1 to -1
        bean.setIntArray(0, -1);
        assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(TestBean.PROP_INT_ARRAY, int1);
        // Test event from -1 to 3
        bean.setIntArray(0, 3);
        assertIndexLoggerEvent(bean, TestBean.PROP_INT_ARRAY, 0, -1, 3, general2, int2, booleanInt1);
        assertNoLoggerEvent(boolean1, general1, int1);
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
        TestBean bean = new TestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(TestBean.PROP_INT_ARRAY, int1);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, boolean1);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, boolean2);
        bean.addPropertyChangeListener(TestBean.PROP_INT_ARRAY, intBoolean1);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, intBoolean1);
        // Test event from false to true
        bean.setBooleanArray(0, true);
        assertIndexLoggerEvent(bean, TestBean.PROP_BOOLEAN_ARRAY, 0, false, true, general1, general2, boolean1, boolean2, intBoolean1);
        assertNoLoggerEvent(int1);
        // Test no event from true to true
        bean.setBooleanArray(0, true);
        assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Test event from true to false
        bean.setBooleanArray(0, false);
        assertIndexLoggerEvent(bean, TestBean.PROP_BOOLEAN_ARRAY, 0, true, false, general1, general2, boolean1, boolean2, intBoolean1);
        assertNoLoggerEvent(int1);
        // Test no event from false to false
        bean.setBooleanArray(0, false);
        assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(TestBean.PROP_BOOLEAN_ARRAY, boolean1);
        // Test event from false to true again with less listeners
        bean.setBooleanArray(0, true);
        assertIndexLoggerEvent(bean, TestBean.PROP_BOOLEAN_ARRAY, 0, false, true, general2, boolean2, intBoolean1);
        assertNoLoggerEvent(int1, general1, boolean1);
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
        TestBean bean = new TestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_VALUE, obj1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_VALUE, obj2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, booleanObj1);
        bean.addPropertyChangeListener(TestBean.PROP_OBJECT_VALUE, booleanObj1);
        // Test event from null to "A"
        bean.setObjectValue("A");
        assertLoggerEvent(bean, TestBean.PROP_OBJECT_VALUE, null, "A", general1, general2, obj1, obj2, booleanObj1);
        assertNoLoggerEvent(boolean1);
        // Test no event from "A" to "A"
        bean.setObjectValue("A");
        assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Test event from "A" to "B"
        bean.setObjectValue("B");
        assertLoggerEvent(bean, TestBean.PROP_OBJECT_VALUE, "A", "B", general1, general2, obj1, obj2, booleanObj1);
        assertNoLoggerEvent(boolean1);
        // Test no event from "B" to "B"
        bean.setObjectValue("B");
        assertNoLoggerEvent(boolean1, general1, general2, obj1, obj2, booleanObj1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(TestBean.PROP_OBJECT_VALUE, obj1);
        // Test event from "B" to "C"
        bean.setObjectValue("C");
        assertLoggerEvent(bean, TestBean.PROP_OBJECT_VALUE, "B", "C", general2, obj2, booleanObj1);
        assertNoLoggerEvent(boolean1, general1, obj1);
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
        TestBean bean = new TestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(TestBean.PROP_INT_VALUE, int1);
        bean.addPropertyChangeListener(TestBean.PROP_INT_VALUE, int2);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, booleanInt1);
        bean.addPropertyChangeListener(TestBean.PROP_INT_VALUE, booleanInt1);
        // Test event from 0 to 2
        bean.setIntValue(2);
        assertLoggerEvent(bean, TestBean.PROP_INT_VALUE, 0, 2, general1, general2, int1, int2, booleanInt1);
        assertNoLoggerEvent(boolean1);
        // Test no event from 2 to 2
        bean.setIntValue(2);
        assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Test event from 2 to -1
        bean.setIntValue(-1);
        assertLoggerEvent(bean, TestBean.PROP_INT_VALUE, 2, -1, general1, general2, int1, int2, booleanInt1);
        assertNoLoggerEvent(boolean1);
        // Test no event from -1 to -1
        bean.setIntValue(-1);
        assertNoLoggerEvent(boolean1, general1, general2, int1, int2, booleanInt1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(TestBean.PROP_INT_VALUE, int1);
        // Test event from -1 to 3
        bean.setIntValue(3);
        assertLoggerEvent(bean, TestBean.PROP_INT_VALUE, -1, 3, general2, int2, booleanInt1);
        assertNoLoggerEvent(boolean1, general1, int1);
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
        TestBean bean = new TestBean();
        bean.addPropertyChangeListener(general1);
        bean.addPropertyChangeListener(general2);
        bean.addPropertyChangeListener(TestBean.PROP_INT_VALUE, int1);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean1);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean2);
        bean.addPropertyChangeListener(TestBean.PROP_INT_VALUE, intBoolean1);
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, intBoolean1);
        // Test event from false to true
        bean.setBooleanValue(true);
        assertLoggerEvent(bean, TestBean.PROP_BOOLEAN_VALUE, false, true, general1, general2, boolean1, boolean2, intBoolean1);
        assertNoLoggerEvent(int1);
        // Test no event from true to true
        bean.setBooleanValue(true);
        assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Test event from true to false
        bean.setBooleanValue(false);
        assertLoggerEvent(bean, TestBean.PROP_BOOLEAN_VALUE, true, false, general1, general2, boolean1, boolean2, intBoolean1);
        assertNoLoggerEvent(int1);
        // Test no event from false to false
        bean.setBooleanValue(false);
        assertNoLoggerEvent(int1, general1, general2, boolean1, boolean2, intBoolean1);
        // Remove some listeners
        bean.removePropertyChangeListener(general1);
        bean.removePropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean1);
        // Test event from false to true again with less listeners
        bean.setBooleanValue(true);
        assertLoggerEvent(bean, TestBean.PROP_BOOLEAN_VALUE, false, true, general2, boolean2, intBoolean1);
        assertNoLoggerEvent(int1, general1, boolean1);
    }
    
    /**
     * Makes sure that the given {@link PropertyChangeListenerLogger} instances
     * have no event logged.
     * @param loggerWithoutEvent The {@link PropertyChangeListenerLogger} to test.
     */
    protected void assertNoLoggerEvent(PropertyChangeListenerLogger... loggerWithoutEvent) {
        for (PropertyChangeListenerLogger logger : loggerWithoutEvent) {
            assertEquals(0, logger.countLog());
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
    protected void assertLoggerEvent(Object expectedSource,
                                     String expectedPropertyName,
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
    protected void assertPropertyChangeEvent(Object expectedSource,
                                             String expectedPropertyName,
                                             Object expectedOldValue,
                                             Object expectedNewVlaue,
                                             PropertyChangeEvent currentEvent) {
        assertFalse(currentEvent instanceof IndexedPropertyChangeEvent);
        assertEquals(expectedSource, currentEvent.getSource());
        assertEquals(expectedPropertyName, currentEvent.getPropertyName());
        assertEquals(expectedOldValue, currentEvent.getOldValue());
        assertEquals(expectedNewVlaue, currentEvent.getNewValue());
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
        TestBean bean = new TestBean();
        assertEquals(0, bean.getPropertyChangeListeners().length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertFalse(bean.hasListeners());
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_INT_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListeners(TestBean.PROP_INT_ARRAY));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        // Add general listener
        PropertyChangeListenerLogger general1 = new PropertyChangeListenerLogger();
        bean.addPropertyChangeListener(general1);
        assertEquals(1, bean.getPropertyChangeListeners().length);
        assertEquals(general1, bean.getPropertyChangeListeners()[0]);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertTrue(bean.hasListeners());
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(TestBean.PROP_INT_VALUE));
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListeners(TestBean.PROP_INT_ARRAY));
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListener(general1));
        // Add boolean listener
        PropertyChangeListenerLogger boolean1 = new PropertyChangeListenerLogger();
        bean.addPropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean1);
        assertEquals(2, bean.getPropertyChangeListeners().length);
        assertEquals(general1, bean.getPropertyChangeListeners()[0]);
        assertEquals(1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_VALUE).length);
        assertEquals(1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertTrue(bean.hasListeners());
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(TestBean.PROP_INT_VALUE));
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListeners(TestBean.PROP_INT_ARRAY));
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertTrue(bean.hasListener(general1));
        assertFalse(bean.hasListener(TestBean.PROP_BOOLEAN_VALUE, general1));
        assertFalse(bean.hasListener(boolean1));
        assertTrue(bean.hasListener(TestBean.PROP_BOOLEAN_VALUE, boolean1));
        assertFalse(bean.hasListener(TestBean.PROP_INT_VALUE, boolean1));
        // Remove general listener
        bean.removePropertyChangeListener(general1);
        assertEquals(1, bean.getPropertyChangeListeners().length);
        assertEquals(1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_VALUE).length);
        assertEquals(1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(boolean1, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE)[0]);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertTrue(bean.hasListeners());
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_INT_VALUE));
        assertTrue(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListeners(TestBean.PROP_INT_ARRAY));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListener(general1));
        assertFalse(bean.hasListener(TestBean.PROP_BOOLEAN_VALUE, general1));
        assertFalse(bean.hasListener(boolean1));
        assertTrue(bean.hasListener(TestBean.PROP_BOOLEAN_VALUE, boolean1));
        assertFalse(bean.hasListener(TestBean.PROP_INT_VALUE, boolean1));
        // Remove boolean listener
        bean.removePropertyChangeListener(TestBean.PROP_BOOLEAN_VALUE, boolean1);
        assertEquals(0, bean.getPropertyChangeListeners().length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_VALUE).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_INT_ARRAY).length);
        assertEquals(0, bean.getPropertyChangeListeners(TestBean.PROP_BOOLEAN_ARRAY).length);
        assertFalse(bean.hasListeners());
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_INT_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_VALUE));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListeners(TestBean.PROP_INT_ARRAY));
        assertFalse(bean.hasListeners(TestBean.PROP_BOOLEAN_ARRAY));
        assertFalse(bean.hasListener(general1));
        assertFalse(bean.hasListener(TestBean.PROP_BOOLEAN_VALUE, general1));
        assertFalse(bean.hasListener(boolean1));
        assertFalse(bean.hasListener(TestBean.PROP_BOOLEAN_VALUE, boolean1));
        assertFalse(bean.hasListener(TestBean.PROP_INT_VALUE, boolean1));
    }
    
    /**
     * The uesed example bean.
     * @author Martin Hentschel
     */
    private static class TestBean extends Bean {
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
         * An object value.
         */
        private Object objectValue;
        
        /**
         * An int value.
         */
        private int intValue;
        
        /**
         * An boolean value.
         */
        private boolean booleanValue;
        
        /**
         * An object array.
         */
        private Object[] objectArray = new Object[2];
        
        /**
         * An int array.
         */
        private int[] intArray = new int[2];
        
        /**
         * An boolean array.
         */
        private boolean[] booleanArray = new boolean[2];

        /**
         * Returns the object value.
         * @return The object value.
         */
        public Object getObjectValue() {
            return objectValue;
        }

        /**
         * Sets the object value.
         * @param objectValue The object value to set.
         */
        public void setObjectValue(Object objectValue) {
            Object oldValue = getObjectValue();
            this.objectValue = objectValue;
            firePropertyChange(PROP_OBJECT_VALUE, oldValue, getObjectValue());
        }

        /**
         * Returns the int value.
         * @return The int value.
         */
        public int getIntValue() {
            return intValue;
        }

        /**
         * Sets the int value.
         * @param intValue The int value to set.
         */
        public void setIntValue(int intValue) {
            int oldValue = getIntValue();
            this.intValue = intValue;
            firePropertyChange(PROP_INT_VALUE, oldValue, getIntValue());
        }

        /**
         * Returns the boolean value.
         * @return The boolean value.
         */
        public boolean isBooleanValue() {
            return booleanValue;
        }

        /**
         * Sets the boolean value.
         * @param booleanValue The boolean value to set.
         */
        public void setBooleanValue(boolean booleanValue) {
            boolean oldValue = isBooleanValue();
            this.booleanValue = booleanValue;
            firePropertyChange(PROP_BOOLEAN_VALUE, oldValue, isBooleanValue());
        }

        /**
         * Returns the object value at the given index.
         * @param index The array index.
         * @return The object value.
         */
        public Object getObjectArray(int index) {
            return objectArray[index];
        }

        /**
         * Sets the object value at the given index.
         * @param index The array index.
         * @param objectValue The value to set.
         */
        public void setObjectArray(int index, Object objectValue) {
            Object oldValue = getObjectArray(index);
            this.objectArray[index] = objectValue;
            fireIndexedPropertyChange(PROP_OBJECT_ARRAY, index, oldValue, getObjectArray(index));
        }

        /**
         * Returns the int value at the given index.
         * @param index The array index.
         * @return The int value.
         */
        public int getIntArray(int index) {
            return intArray[index];
        }

        /**
         * Sets the int value at the given index.
         * @param index The array index.
         * @param intValue The value to set.
         */
        public void setIntArray(int index, int intValue) {
            int oldValue = getIntArray(index);
            this.intArray[index] = intValue;
            fireIndexedPropertyChange(PROP_INT_ARRAY, index, oldValue, getIntArray(index));
        }

        /**
         * Returns the boolean value at the given index.
         * @param index The array index.
         * @return The boolean value.
         */
        public boolean getBooleanArray(int index) {
            return booleanArray[index];
        }

        /**
         * Sets the boolean value at the given index.
         * @param index The array index.
         * @param booleanValue The boolean value to set.
         */
        public void setBooleanArray(int index, boolean booleanValue) {
            boolean oldValue = getBooleanArray(index);
            this.booleanArray[index] = booleanValue;
            fireIndexedPropertyChange(PROP_BOOLEAN_ARRAY, index, oldValue, getBooleanArray(index));
        }
        
        /**
         * Fires an invalid event.
         */
        public void fireInvalidEvent() {
            firePropertyChange(new PropertyChangeEvent(this, "INVALID", "INVALID_OLD", "INVALID_NEW"));
        }
    }
}
