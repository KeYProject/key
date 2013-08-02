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

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Comparator;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.test.model.ClassA;
import org.key_project.util.test.model.ClassB;

/**
 * Tests for {@link ObjectUtil}
 * @author Martin Hentschel
 */
public class ObjectUtilTest extends TestCase {
   /**
    * Tests {@link ObjectUtil#getClass()}.
    */
   @Test
   public void testGetClass() {
      assertNull(ObjectUtil.getClass(null));
      assertEquals(String.class, "A".getClass());
   }

   /**
    * Tests {@link ObjectUtil#createEqualsComparator()}.
    */
   @Test
   public void testCreateEqualsComparator() {
       Comparator<String> c = ObjectUtil.createEqualsComparator();
       assertNotNull(c);
       assertSame(0, c.compare("A", "A"));
       assertNotSame(0, c.compare("A", "a"));
       assertNotSame(0, c.compare("a", "b"));
       assertNotSame(0, c.compare("a", null));
       assertNotSame(0, c.compare(null, "b"));
       assertSame(0, c.compare(null, null));
   }
    
   /**
    * Tests for {@link ObjectUtil#hashCode()}
    */
   @Test
   public void testHashCode() {
      assertEquals(0, ObjectUtil.hashCode(null));
      Object obj = new Object();
      assertEquals(obj.hashCode(), ObjectUtil.hashCode(obj));
      assertEquals("A".hashCode(), ObjectUtil.hashCode("A"));
      assertNotSame("A".hashCode(), ObjectUtil.hashCode(obj));
   }
   
   /**
    * Tests {@link ObjectUtil#get(Object, Field)},
    * {@link ObjectUtil#set(Object, Field, Object)} and
    * {@link ObjectUtil#set(Object, Field, boolean)} and
    * {@link ObjectUtil#set(Object, Field, int)}.
    */
   @Test
   public void testGetAndSet_Object_Field() {
      ClassA.staticField = -42;
      ClassA.staticBooleanField = false;
      ClassA a = new ClassA();
      ClassB b = new ClassB();
      // Test null object
      try {
         ObjectUtil.get(null, ObjectUtil.findField(ClassA.class, "privateField"));
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Object is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, ObjectUtil.findField(ClassA.class, "staticField"), -4711);
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, ObjectUtil.findField(ClassA.class, "staticBooleanField"), true);
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      
      // Test null field
      try {
         ObjectUtil.get(a, (Field)null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, (Field)null, null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, (Field)null, true);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, (Field)null, 42);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      
      try {
         // Test returned values in A
         assertEquals(1, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "privateField")));
         assertEquals(2, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "protectedField")));
         assertEquals(3, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "publicField")));
         assertEquals(4, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "defaultField")));
         assertEquals("A", ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "onlyInA")));
         assertEquals(true, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "booleanField")));
         assertEquals(-4711, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "staticField")));
         assertEquals(true, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "staticBooleanField")));
         // Change values in A
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "privateField"), 42);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "protectedField"), 43);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "publicField"), 44);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "defaultField"), 45);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "onlyInA"), "Changed");
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "booleanField"), false);
         // Test returned values in A again
         assertEquals(42, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "privateField")));
         assertEquals(43, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "protectedField")));
         assertEquals(44, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "publicField")));
         assertEquals(45, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "defaultField")));
         assertEquals("Changed", ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "onlyInA")));
         assertEquals(false, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "booleanField")));
         // Change values in A second time
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "privateField"), -42);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "protectedField"), -43);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "publicField"), -44);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "defaultField"), -45);
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "onlyInA"), "ChangedAgain");
         ObjectUtil.set(a, ObjectUtil.findField(ClassA.class, "booleanField"), true);
         // Test returned values in A again
         assertEquals(-42, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "privateField")));
         assertEquals(-43, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "protectedField")));
         assertEquals(-44, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "publicField")));
         assertEquals(-45, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "defaultField")));
         assertEquals("ChangedAgain", ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "onlyInA")));
         assertEquals(true, ObjectUtil.get(a, ObjectUtil.findField(ClassA.class, "booleanField")));
         // Test returned values in B
         assertEquals(1, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "privateField")));
         assertEquals(2, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "protectedField")));
         assertEquals(3, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "publicField")));
         assertEquals(4, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "defaultField")));
         assertEquals("A", ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "onlyInA")));
         assertEquals(true, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "booleanField")));
         assertEquals(42, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "privateField")));
         assertEquals(43, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "protectedField")));
         assertEquals(44, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "publicField")));
         assertEquals(45, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "defaultField")));
         assertEquals("B", ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "onlyInB")));
         // Change values in B
         ObjectUtil.set(b, ObjectUtil.findField(ClassA.class, "privateField"), 42);
         ObjectUtil.set(b, ObjectUtil.findField(ClassA.class, "protectedField"), 43);
         ObjectUtil.set(b, ObjectUtil.findField(ClassA.class, "publicField"), 44);
         ObjectUtil.set(b, ObjectUtil.findField(ClassA.class, "defaultField"), 45);
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "onlyInA"), "ChangedA");
         ObjectUtil.set(b, ObjectUtil.findField(ClassA.class, "booleanField"), false);
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "privateField"), 46);
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "protectedField"), 47);
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "publicField"), 48);
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "defaultField"), 49);
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "onlyInB"), "ChangedB");
         // Test returned values in B again
         assertEquals(42, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "privateField")));
         assertEquals(43, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "protectedField")));
         assertEquals(44, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "publicField")));
         assertEquals(45, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "defaultField")));
         assertEquals("ChangedA", ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "onlyInA")));
         assertEquals(false, ObjectUtil.get(b, ObjectUtil.findField(ClassA.class, "booleanField")));
         assertEquals(46, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "privateField")));
         assertEquals(47, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "protectedField")));
         assertEquals(48, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "publicField")));
         assertEquals(49, ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "defaultField")));
         assertEquals("ChangedB", ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "onlyInB")));
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test invalid fields
      try {
         ObjectUtil.get(b, ObjectUtil.findField(ClassB.class, "INVALID"));
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "INVALID"), null);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "INVALID"), true);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, ObjectUtil.findField(ClassB.class, "INVALID"), 42);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests {@link ObjectUtil#get(Object, String)},
    * {@link ObjectUtil#set(Object, String, Object)} and
    * {@link ObjectUtil#set(Object, String, boolean)} and
    * {@link ObjectUtil#set(Object, String, int)}.
    */
   @Test
   public void testGetAndSet_Object_String() {
      ClassA a = new ClassA();
      ClassB b = new ClassB();
      // Test null object
      try {
         ObjectUtil.get(null, "privateField");
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Object is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, "privateField", null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Object is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, "privateField", true);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Object is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, "privateField", 42);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Object is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      
      // Test null field
      try {
         ObjectUtil.get(a, (String)null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, (String)null, null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, (String)null, true);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, (String)null, 42);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      
      try {
         // Test returned values in A
         assertEquals(1, ObjectUtil.get(a, "privateField"));
         assertEquals(2, ObjectUtil.get(a, "protectedField"));
         assertEquals(3, ObjectUtil.get(a, "publicField"));
         assertEquals(4, ObjectUtil.get(a, "defaultField"));
         assertEquals("A", ObjectUtil.get(a, "onlyInA"));
         assertEquals(true, ObjectUtil.get(a, "booleanField"));
         // Change values in A
         ObjectUtil.set(a, "privateField", 42);
         ObjectUtil.set(a, "protectedField", 43);
         ObjectUtil.set(a, "publicField", 44);
         ObjectUtil.set(a, "defaultField", 45);
         ObjectUtil.set(a, "onlyInA", "Changed");
         ObjectUtil.set(a, "booleanField", false);
         // Test returned values in A again
         assertEquals(42, ObjectUtil.get(a, "privateField"));
         assertEquals(43, ObjectUtil.get(a, "protectedField"));
         assertEquals(44, ObjectUtil.get(a, "publicField"));
         assertEquals(45, ObjectUtil.get(a, "defaultField"));
         assertEquals("Changed", ObjectUtil.get(a, "onlyInA"));
         assertEquals(false, ObjectUtil.get(a, "booleanField"));
         // Change values in A again
         ObjectUtil.set(a, "privateField", -42);
         ObjectUtil.set(a, "protectedField", -43);
         ObjectUtil.set(a, "publicField", -44);
         ObjectUtil.set(a, "defaultField", -45);
         ObjectUtil.set(a, "onlyInA", "ChangedAgain");
         ObjectUtil.set(a, "booleanField", true);
         // Test returned values in A again
         assertEquals(-42, ObjectUtil.get(a, "privateField"));
         assertEquals(-43, ObjectUtil.get(a, "protectedField"));
         assertEquals(-44, ObjectUtil.get(a, "publicField"));
         assertEquals(-45, ObjectUtil.get(a, "defaultField"));
         assertEquals("ChangedAgain", ObjectUtil.get(a, "onlyInA"));
         assertEquals(true, ObjectUtil.get(a, "booleanField"));
         // Test returned values in B
         assertEquals("A", ObjectUtil.get(b, "onlyInA"));
         assertEquals(42, ObjectUtil.get(b, "privateField"));
         assertEquals(43, ObjectUtil.get(b, "protectedField"));
         assertEquals(44, ObjectUtil.get(b, "publicField"));
         assertEquals(45, ObjectUtil.get(b, "defaultField"));
         assertEquals("B", ObjectUtil.get(b, "onlyInB"));
         // Change values in B
         ObjectUtil.set(b, "onlyInA", "ChangedInA");
         ObjectUtil.set(b, "privateField", -43);
         ObjectUtil.set(b, "protectedField", -44);
         ObjectUtil.set(b, "publicField", -45);
         ObjectUtil.set(b, "defaultField", -46);
         ObjectUtil.set(b, "onlyInB", "ChangedInB");
         // Test returned values in B again
         assertEquals("ChangedInA", ObjectUtil.get(b, "onlyInA"));
         assertEquals(-43, ObjectUtil.get(b, "privateField"));
         assertEquals(-44, ObjectUtil.get(b, "protectedField"));
         assertEquals(-45, ObjectUtil.get(b, "publicField"));
         assertEquals(-46, ObjectUtil.get(b, "defaultField"));
         assertEquals("ChangedInB", ObjectUtil.get(b, "onlyInB"));
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test invalid fields
      try {
         ObjectUtil.get(b, "INVALID");
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, "INVALID", null);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, "INVALID", true);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, "INVALID", 42);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests {@link ObjectUtil#get(Object, Class, String)},
    * {@link ObjectUtil#set(Object, Class, String, Object)} and
    * {@link ObjectUtil#set(Object, Class, String, boolean)} and
    * {@link ObjectUtil#set(Object, Class, String, int)}.
    */
   @Test
   public void testGetAndSet_Object_Class_String() {
      ClassA.staticField = -42;
      ClassA.staticBooleanField = false;
      ClassA.staticStringField = null;
      ClassA a = new ClassA();
      ClassB b = new ClassB();
      // Test null object
      try {
         ObjectUtil.get(null, a.getClass(), "privateField");
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Object is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, a.getClass(), "staticBooleanField", true);
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, a.getClass(), "staticStringField", "Hello");
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(null, a.getClass(), "staticField", -4711);
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }

      // Test null class
      try {
         ObjectUtil.get(a, null, "privateField");
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Class is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, null, "privateField", null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Class is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, null, "privateField", true);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Class is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, null, "privateField", 42);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Class is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }

      // Test null field
      try {
         ObjectUtil.get(a, a.getClass(), null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, a.getClass(), null, null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, a.getClass(), null, true);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(a, a.getClass(), null, 42);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      
      try {
         // Test returned values in A
         assertEquals(1, ObjectUtil.get(a, ClassA.class, "privateField"));
         assertEquals(2, ObjectUtil.get(a, ClassA.class, "protectedField"));
         assertEquals(3, ObjectUtil.get(a, ClassA.class, "publicField"));
         assertEquals(4, ObjectUtil.get(a, ClassA.class, "defaultField"));
         assertEquals("A", ObjectUtil.get(a, ClassA.class, "onlyInA"));
         assertEquals(true, ObjectUtil.get(a, ClassA.class, "booleanField"));
         assertEquals(-4711, ObjectUtil.get(a, ClassA.class, "staticField"));
         assertEquals(true, ObjectUtil.get(a, ClassA.class, "staticBooleanField"));
         assertEquals("Hello", ObjectUtil.get(a, ClassA.class, "staticStringField"));
         // Change values in A
         ObjectUtil.set(a, ClassA.class, "privateField", 42);
         ObjectUtil.set(a, ClassA.class, "protectedField", 43);
         ObjectUtil.set(a, ClassA.class, "publicField", 44);
         ObjectUtil.set(a, ClassA.class, "defaultField", 45);
         ObjectUtil.set(a, ClassA.class, "onlyInA", "Changed");
         ObjectUtil.set(a, ClassA.class, "booleanField", false);
         // Test returned values in A again
         assertEquals(42, ObjectUtil.get(a, ClassA.class, "privateField"));
         assertEquals(43, ObjectUtil.get(a, ClassA.class, "protectedField"));
         assertEquals(44, ObjectUtil.get(a, ClassA.class, "publicField"));
         assertEquals(45, ObjectUtil.get(a, ClassA.class, "defaultField"));
         assertEquals("Changed", ObjectUtil.get(a, ClassA.class, "onlyInA"));
         assertEquals(false, ObjectUtil.get(a, ClassA.class, "booleanField"));
         // Change values in A again
         ObjectUtil.set(a, ClassA.class, "privateField", -42);
         ObjectUtil.set(a, ClassA.class, "protectedField", -43);
         ObjectUtil.set(a, ClassA.class, "publicField", -44);
         ObjectUtil.set(a, ClassA.class, "defaultField", -45);
         ObjectUtil.set(a, ClassA.class, "onlyInA", "ChangedAgain");
         ObjectUtil.set(a, ClassA.class, "booleanField", true);
         // Test returned values in A again
         assertEquals(-42, ObjectUtil.get(a, ClassA.class, "privateField"));
         assertEquals(-43, ObjectUtil.get(a, ClassA.class, "protectedField"));
         assertEquals(-44, ObjectUtil.get(a, ClassA.class, "publicField"));
         assertEquals(-45, ObjectUtil.get(a, ClassA.class, "defaultField"));
         assertEquals("ChangedAgain", ObjectUtil.get(a, ClassA.class, "onlyInA"));
         assertEquals(true, ObjectUtil.get(a, ClassA.class, "booleanField"));
         // Test returned values in B
         assertEquals(1, ObjectUtil.get(b, ClassA.class, "privateField"));
         assertEquals(2, ObjectUtil.get(b, ClassA.class, "protectedField"));
         assertEquals(3, ObjectUtil.get(b, ClassA.class, "publicField"));
         assertEquals(4, ObjectUtil.get(b, ClassA.class, "defaultField"));
         assertEquals("A", ObjectUtil.get(b, ClassA.class, "onlyInA"));
         assertEquals(true, ObjectUtil.get(b, ClassA.class, "booleanField"));
         assertEquals(42, ObjectUtil.get(b, ClassB.class, "privateField"));
         assertEquals(43, ObjectUtil.get(b, ClassB.class, "protectedField"));
         assertEquals(44, ObjectUtil.get(b, ClassB.class, "publicField"));
         assertEquals(45, ObjectUtil.get(b, ClassB.class, "defaultField"));
         assertEquals("B", ObjectUtil.get(b, ClassB.class, "onlyInB"));
         // Change values in B
         ObjectUtil.set(b, ClassA.class, "privateField", 42);
         ObjectUtil.set(b, ClassA.class, "protectedField", 43);
         ObjectUtil.set(b, ClassA.class, "publicField", 44);
         ObjectUtil.set(b, ClassA.class, "defaultField", 45);
         ObjectUtil.set(b, ClassA.class, "onlyInA", "ChangedInA");
         ObjectUtil.set(b, ClassA.class, "booleanField", false);
         ObjectUtil.set(b, ClassB.class, "privateField", 46);
         ObjectUtil.set(b, ClassB.class, "protectedField", 47);
         ObjectUtil.set(b, ClassB.class, "publicField", 48);
         ObjectUtil.set(b, ClassB.class, "defaultField", 49);
         ObjectUtil.set(b, ClassB.class, "onlyInB", "ChangedInB");
         // Test returned values in B again
         assertEquals(42, ObjectUtil.get(b, ClassA.class, "privateField"));
         assertEquals(43, ObjectUtil.get(b, ClassA.class, "protectedField"));
         assertEquals(44, ObjectUtil.get(b, ClassA.class, "publicField"));
         assertEquals(45, ObjectUtil.get(b, ClassA.class, "defaultField"));
         assertEquals("ChangedInA", ObjectUtil.get(b, ClassA.class, "onlyInA"));
         assertEquals(false, ObjectUtil.get(b, ClassA.class, "booleanField"));
         assertEquals(46, ObjectUtil.get(b, ClassB.class, "privateField"));
         assertEquals(47, ObjectUtil.get(b, ClassB.class, "protectedField"));
         assertEquals(48, ObjectUtil.get(b, ClassB.class, "publicField"));
         assertEquals(49, ObjectUtil.get(b, ClassB.class, "defaultField"));
         assertEquals("ChangedInB", ObjectUtil.get(b, ClassB.class, "onlyInB"));
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      
      // Test invalid fields
      try {
         ObjectUtil.get(b, ClassB.class, "INVALID");
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, ClassB.class, "INVALID", null);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, ClassB.class, "INVALID", true);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.set(b, ClassB.class, "INVALID", 42);
      }
      catch (NoSuchFieldException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests {@link ObjectUtil#findField(Class, String)}
    */
   @Test
   public void testFindField() {
      // Test null class 
      try {
         ObjectUtil.findField(null, "privateField");
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Class is undefined (null).", e.getMessage());
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test null field 
      try {
         ObjectUtil.findField(ClassA.class, null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Field is undefined (null).", e.getMessage());
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }      
      // Test valid fields
      try {
         compareField("privateField", ObjectUtil.findField(ClassA.class, "privateField"));
         compareField("protectedField", ObjectUtil.findField(ClassA.class, "protectedField"));
         compareField("publicField", ObjectUtil.findField(ClassA.class, "publicField"));
         compareField("defaultField", ObjectUtil.findField(ClassA.class, "defaultField"));
         compareField("onlyInA", ObjectUtil.findField(ClassA.class, "onlyInA"));
         compareField("privateField", ObjectUtil.findField(ClassB.class, "privateField"));
         compareField("protectedField", ObjectUtil.findField(ClassB.class, "protectedField"));
         compareField("publicField", ObjectUtil.findField(ClassB.class, "publicField"));
         compareField("defaultField", ObjectUtil.findField(ClassB.class, "defaultField"));
         compareField("onlyInA", ObjectUtil.findField(ClassB.class, "onlyInA"));
         compareField("onlyInB", ObjectUtil.findField(ClassB.class, "onlyInB"));
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test invalid fields
      try {
         ObjectUtil.findField(ClassA.class, "INVALID");
      }
      catch (NoSuchFieldException e) {
      }
   }
   
   /**
    * Compares the field.
    * @param expectedField The expected field name.
    * @param currentField The current field.
    */
   protected void compareField(String expectedField, Field currentField) {
      assertNotNull(currentField);
      assertEquals(expectedField, currentField.getName());
   }
   
   /**
    * Tests {@link ObjectUtil#invoke(Object, String, Object...)} and
    * {@link ObjectUtil#invoke(Object, Method, Object...)}
    */
   @Test
   public void testInvoke() {
      ClassA a = new ClassA();
      ClassB b = new ClassB();
      // Test null class
      try {
         ObjectUtil.invoke(null, "getDefault");
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Object is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test null string method
      try {
         ObjectUtil.invoke(a, (String)null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Method is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }      
      // Test null method instance
      try {
         ObjectUtil.invoke(a, (Method)null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Method is undefined (null).", e.getMessage());
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }            
      // Test valid calls
      try {
         assertEquals(45, ObjectUtil.invoke(a, "getDefault"));
         assertEquals(42, ObjectUtil.invoke(a, "getPrivate"));
         assertEquals(43, ObjectUtil.invoke(a, "getPublic"));
         assertEquals(44, ObjectUtil.invoke(a, "getProtected"));
         assertEquals(11, ObjectUtil.invoke(a, "getValue", 11));
         assertEquals(7, ObjectUtil.invoke(a, "getValue", 3, 4));
         assertEquals("A", ObjectUtil.invoke(a, "onlyInA"));
         assertEquals(42, ObjectUtil.invoke(a, "getPrivate"));
         assertEquals(665, ObjectUtil.invoke(b, "getDefault"));
         assertEquals(662, ObjectUtil.invoke(b, "getPrivate"));
         assertEquals(663, ObjectUtil.invoke(b, "getPublic"));
         assertEquals(664, ObjectUtil.invoke(b, "getProtected"));
         assertEquals(11, ObjectUtil.invoke(b, "getValue", 11));
         assertEquals(7, ObjectUtil.invoke(b, "getValue", 3, 4));
         assertEquals("A", ObjectUtil.invoke(b, "onlyInA"));
         assertEquals(662, ObjectUtil.invoke(b, "getPrivate"));
         assertEquals("B", ObjectUtil.invoke(b, "onlyInB"));
      }
      catch (IllegalArgumentException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (NoSuchMethodException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (IllegalAccessException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (InvocationTargetException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test invalid methods
      try {
         ObjectUtil.invoke(a, "INVALID");
      }
      catch (NoSuchMethodException e) {
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      try {
         ObjectUtil.invoke(a, "getDefault", "A");
      }
      catch (NoSuchMethodException e) {
      }      
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests {@link ObjectUtil#findMethod(Class, String, Class...)}
    */
   @Test
   public void testFindMethod() {
      // Test null class 
      try {
         ObjectUtil.findMethod(null, "getPrivate");
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Class is undefined (null).", e.getMessage());
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test null method 
      try {
         ObjectUtil.findMethod(ClassA.class, null);
         fail();
      }
      catch (IllegalArgumentException e) {
         assertEquals("Method is undefined (null).", e.getMessage());
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }      
      // Test valid methods
      try {
         compareMethod("getDefault", ObjectUtil.findMethod(ClassA.class, "getDefault"));
         compareMethod("getPrivate", ObjectUtil.findMethod(ClassA.class, "getPrivate"));
         compareMethod("getPublic", ObjectUtil.findMethod(ClassA.class, "getPublic"));
         compareMethod("getProtected", ObjectUtil.findMethod(ClassA.class, "getProtected"));
         compareMethod("getValue", ObjectUtil.findMethod(ClassA.class, "getValue", Integer.class));
         compareMethod("getValue", ObjectUtil.findMethod(ClassA.class, "getValue", Integer.class, Integer.class));
         compareMethod("onlyInA", ObjectUtil.findMethod(ClassA.class, "onlyInA"));
         compareMethod("getDefault", ObjectUtil.findMethod(ClassB.class, "getDefault"));
         compareMethod("getPrivate", ObjectUtil.findMethod(ClassB.class, "getPrivate"));
         compareMethod("getPublic", ObjectUtil.findMethod(ClassB.class, "getPublic"));
         compareMethod("getProtected", ObjectUtil.findMethod(ClassB.class, "getProtected"));
         compareMethod("getValue", ObjectUtil.findMethod(ClassB.class, "getValue", Integer.class));
         compareMethod("getValue", ObjectUtil.findMethod(ClassB.class, "getValue", Integer.class, Integer.class));
         compareMethod("onlyInA", ObjectUtil.findMethod(ClassB.class, "onlyInA"));
         compareMethod("onlyInB", ObjectUtil.findMethod(ClassB.class, "onlyInB"));
      }
      catch (Exception e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      // Test invalid methods
      try {
         ObjectUtil.findMethod(ClassA.class, "INVALID");
      }
      catch (NoSuchMethodException e) {
      }
      try {
         ObjectUtil.findMethod(ClassB.class, "getDefault", String.class);
      }
      catch (NoSuchMethodException e) {
      }
   }
   
   /**
    * Compares the method.
    * @param expectedName The expected method name.
    * @param currentMethod The current method.
    */
   protected void compareMethod(String expectedName, Method currentMethod) {
      assertNotNull(currentMethod);
      assertEquals(expectedName, currentMethod.getName());
   }
   
   /**
    * Tests {@link ObjectUtil#toString(Object)}
    */
   @Test
   public void testToString() {
      assertNull(ObjectUtil.toString(null));
      assertEquals("A", ObjectUtil.toString("A"));
   }
   
   /**
    * Tests {@link ObjectUtil#equals(Object, Object)}
    */
   @Test
   public void testEquals() {
      assertTrue(ObjectUtil.equals(null, null));
      assertFalse(ObjectUtil.equals(null, "A"));
      assertFalse(ObjectUtil.equals("A", null));
      assertTrue(ObjectUtil.equals("A", "A"));
      assertFalse(ObjectUtil.equals("A", "B"));
      assertFalse(ObjectUtil.equals("B", "A"));
      assertTrue(ObjectUtil.equals("B", "B"));
   }
}