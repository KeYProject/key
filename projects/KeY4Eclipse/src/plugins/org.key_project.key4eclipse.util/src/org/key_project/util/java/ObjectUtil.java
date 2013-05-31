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

package org.key_project.util.java;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

/**
 * Provides static methods to work with objects.
 * @author Martin Hentschel
 */
public final class ObjectUtil {
   /**
    * Forbid instances by this private constructor.
    */
   private ObjectUtil() {
   }
   
   /**
    * Returns the value from the field.
    * @param <T> The value type.
    * @param obj The object to read from.
    * @param fieldName The name of the field.
    * @return The field value.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static <T> T get(Object obj, String fieldName) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      return get(obj, obj.getClass(), fieldName);
   }
   
   /**
    * Returns the value from the field.
    * @param <T> The value type.
    * @param obj The object to read from.
    * @param classInstance The class in that the field is declared.
    * @param fieldName The name of the field.
    * @return The field value.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static <T> T get(Object obj, Class<?> classInstance, String fieldName) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      Field field = findField(classInstance, fieldName);
      return get(obj, field);
   }
   
   /**
    * Returns the value from the field.
    * @param <T> The value type.
    * @param obj The object to read from.
    * @param field The {@link Field} to read.
    * @return The field value.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   @SuppressWarnings("unchecked")
   public static <T> T get(Object obj, Field field) throws IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      if (field == null) {
         throw new IllegalArgumentException("Field is undefined (null).");
      }
      boolean oldAccessible = field.isAccessible();
      try {
         field.setAccessible(true);
         return (T)field.get(obj);
      }
      finally {
         field.setAccessible(oldAccessible);
      }
   }
   
   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param fieldName The name of the field.
    * @param value The value to write.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, String fieldName, Object value) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      set(obj, obj.getClass(), fieldName, value);
   }

   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param classInstance The class in that the field is declared.
    * @param fieldName The name of the field.
    * @param value The value to write.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, Class<?> classInstance, String fieldName, Object value) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      Field field = findField(classInstance, fieldName);
      set(obj, field, value);
   }

   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param field The {@link Field} to write to.
    * @param value The value to write.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, Field field, Object value) throws IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      if (field == null) {
         throw new IllegalArgumentException("Field is undefined (null).");
      }
      boolean oldAccessible = field.isAccessible();
      try {
         field.setAccessible(true);
         field.set(obj, value);
      }
      finally {
         field.setAccessible(oldAccessible);
      }
   }
   
   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param fieldName The name of the field.
    * @param value The value to write.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, String fieldName, boolean value) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      set(obj, obj.getClass(), fieldName, value);
   }
   
   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param classInstance The class in that the field is declared.
    * @param fieldName The name of the field.
    * @param value The value to write.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, Class<?> classInstance, String fieldName, boolean value) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      Field field = findField(classInstance, fieldName);
      set(obj, field, value);
   }
   
   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param field The {@link Field} to write to.
    * @param value The value to write.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, Field field, boolean value) throws IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      if (field == null) {
         throw new IllegalArgumentException("Field is undefined (null).");
      }
      boolean oldAccessible = field.isAccessible();
      try {
         field.setAccessible(true);
         field.setBoolean(obj, value);
      }
      finally {
         field.setAccessible(oldAccessible);
      }
   }
   
   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param fieldName The name of the field.
    * @param value The value to write.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, String fieldName, int value) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      set(obj, obj.getClass(), fieldName, value);
   }
   
   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param classInstance The class in that the field is declared.
    * @param fieldName The name of the field.
    * @param value The value to write.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, Class<?> classInstance, String fieldName, int value) throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
      Field field = findField(classInstance, fieldName);
      set(obj, field, value);
   }
   
   /**
    * Sets the value of the given field on the given {@link Object}.
    * @param obj The object to write to.
    * @param field The {@link Field} to write to.
    * @param value The value to write.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    */
   public static void set(Object obj, Field field, int value) throws IllegalArgumentException, IllegalAccessException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      if (field == null) {
         throw new IllegalArgumentException("Field is undefined (null).");
      }
      boolean oldAccessible = field.isAccessible();
      try {
         field.setAccessible(true);
         field.setInt(obj, value);
      }
      finally {
         field.setAccessible(oldAccessible);
      }
   }

   /**
    * Finds the {@link Field} with the name inside the given {@link Class}.
    * @param classInstance The {@link Class} to search in.
    * @param fieldName The name of the field.
    * @return The found {@link Field}.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    */
   public static Field findField(Class<?> classInstance, String fieldName) throws SecurityException, NoSuchFieldException {
      if (classInstance != null) {
         try {
            if (!StringUtil.isEmpty(fieldName)) {
               return classInstance.getDeclaredField(fieldName);
            }
            else {
               throw new IllegalArgumentException("Field is undefined (null).");
            }
         }
         catch (NoSuchFieldException e) {
            if (classInstance.getSuperclass() != null) {
               return findField(classInstance.getSuperclass(), fieldName);
            }
            else {
               throw e;
            }
         }
      }
      else {
         throw new IllegalArgumentException("Class is undefined (null).");
      }
   }

   /**
    * Executes the method on the given {@link Object}.
    * @param <T> The return type
    * @param obj The {@link Object} to execute on.
    * @param methodName
    * @param parameters The method parameters.
    * @return The method result.
    * @throws NoSuchMethodException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    * @throws InvocationTargetException Occurred Exception.
    */
   public static <T> T invoke(Object obj, String methodName, Object... parameters) throws NoSuchMethodException, IllegalArgumentException, IllegalAccessException, InvocationTargetException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      List<Class<?>> parameterClasses = new LinkedList<Class<?>>();
      for (Object parameter : parameters) {
         parameterClasses.add(parameter.getClass());
      }
      Method method = findMethod(obj.getClass(), methodName, parameterClasses.toArray(new Class[parameterClasses.size()]));
      return invoke(obj, method, parameters);
   }
   
   /**
    * Executes the method on the given {@link Object}.
    * @param <T> The return type
    * @param obj The {@link Object} to execute on.
    * @param method The {@link Method} to execute.
    * @param parameters The method parameters.
    * @return The method result.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    * @throws InvocationTargetException Occurred Exception.
    */
   @SuppressWarnings("unchecked")
   public static <T> T invoke(Object obj, Method method, Object... parameters) throws IllegalArgumentException, IllegalAccessException, InvocationTargetException {
      if (obj == null) {
         throw new IllegalArgumentException("Object is undefined (null).");
      }
      if (method == null) {
         throw new IllegalArgumentException("Method is undefined (null).");
      }
      boolean oldAccessible = method.isAccessible();
      try {
         method.setAccessible(true);
         return (T)method.invoke(obj, parameters);
      }
      finally {
         method.setAccessible(oldAccessible);
      }
   }
   
   /**
    * Finds the {@link Method} in the given {@link Class}.
    * @param classInstance The {@link Class} to search in.
    * @param methodName The method name to search.
    * @param parameterClasses The parameter {@link Class}es.
    * @return The found {@link Method}.
    * @throws NoSuchMethodException Occurred Exception
    */
   public static Method findMethod(Class<?> classInstance, String methodName, @SuppressWarnings("rawtypes") Class... parameterClasses) throws NoSuchMethodException {
      if (classInstance != null) {
         try {
            if (!StringUtil.isEmpty(methodName)) {
               return classInstance.getDeclaredMethod(methodName, parameterClasses);
            }
            else {
               throw new IllegalArgumentException("Method is undefined (null).");
            }
         }
         catch (NoSuchMethodException e) {
            if (classInstance.getSuperclass() != null) {
               return findMethod(classInstance.getSuperclass(), methodName, parameterClasses);
            }
            else {
               throw e;
            }
         }
      }
      else {
         throw new IllegalArgumentException("Class is undefined (null).");
      }
   }

   /**
    * Nullpointer save execution of {@link Object#equals(Object)}.
    * The two objects are also equal if both references are {@code null}
    * @param first The first {@link Object}.
    * @param second The second {@link Object}.
    * @return {@code true} objects are equal or both {@code null}, {@code false} otherwise
    */
   public static boolean equals(Object first, Object second) {
      if (first != null) {
         if (second != null) {
            return first.equals(second);
         }
         else {
            return false;
         }
      }
      else {
         return second == null;
      }
   }

   /**
    * Nullpointer save execution of {@link Object#toString()}.
    * @param obj The object to execute to string on.
    * @return The string value or {@code null} if the object is {@code null}.
    */
   public static String toString(Object obj) {
      if (obj != null) {
         return obj.toString();
      }
      else {
         return null;
      }
   }

   /**
    * Nullpointer save execution of {@link Object#hashCode()}
    * @param obj The object to get the hashcode from.
    * @return The hashcode that is might {@code 0} if the object was {@code null}.
    */
   public static int hashCode(Object obj) {
      return obj != null ? obj.hashCode() : 0;
   }
   
   /**
    * Creates a {@link Comparator} that can be used to compute the
    * equality of two given {@link Object}s. They are seen as equal
    * if {@link ObjectUtil#equals(Object, Object)} tells it. In this case
    * {@code 0} is returned in {@link Comparator#compare(Object, Object)}.
    * If they are not equal {@link Comparator#compare(Object, Object)} returns
    * a value different to {@code 0}.
    * @return The created {@link Comparator}.
    */
   public static <T> Comparator<T> createEqualsComparator() {
       return new Comparator<T>() {
           @Override
           public int compare(T arg0, T arg1) {
               return ObjectUtil.equals(arg0, arg1) ? 0 : 1;
           }
       };
   }

   /**
    * Nullpointer save execution of {@link Object#getClass()}.
    * @param obj The object to execute get class on.
    * @return The {@link Class} or {@code null} if the object is {@code null}.
    */
   public static Class<?> getClass(Object obj) {
      return obj != null ? obj.getClass() : null;
   }
}