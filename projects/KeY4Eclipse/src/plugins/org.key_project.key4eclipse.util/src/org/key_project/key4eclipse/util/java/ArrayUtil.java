/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.java;


/**
 * Provides static methods to work with arrays.
 * @author Martin Hentschel
 */
public final class ArrayUtil {
   /**
    * Forbid instances by this private constructor.
    */
   private ArrayUtil() {
   }
   
   /**
    * <p>
    * Adds the given element to the existing array. The result is a new
    * array that contains one more element.
    * </p>
    * <p>
    * <b>Attention: </b> It is not possible to use this method with
    * two {@code null} parameters. In this case is an {@link IllegalArgumentException}
    * thrown.
    * </p>
    * @param array The array to extend.
    * @param toAddT The element to add.
    * @return The new created array with one more element.
    * @throws IllegalArgumentException Both parameters are {@code null}.
    */
   @SuppressWarnings("unchecked")
   public static <T> T[] add(T[] array, T toAdd) {
       if (array != null) {
           T[] result = (T[])java.lang.reflect.Array.newInstance(array.getClass().getComponentType(), array.length + 1);
           for (int i = 0; i < array.length; i++) {
               result[i] = array[i];
           }
           result[array.length] = toAdd;
           return result;
       }
       else {
           if (toAdd != null) {
               T[] result = (T[])java.lang.reflect.Array.newInstance(toAdd.getClass(), 1);
               result[0] = toAdd;
               return result;
           }
           else {
               throw new IllegalArgumentException("Can not create an array if both paramters are null.");
           }
       }
   }

   /**
    * Checks if the given array contains the element to search.
    * @param <T> The type of the array.
    * @param array The array.
    * @param toSearch The element to search.
    * @return {@code true} if the array contains the element or {@code false} if not or if the array is {@code null}.
    */
   public static <T> boolean contains(T[] array, T toSearch) {
      boolean contains = false;
      if (array != null) {
         int i = 0;
         while (i < array.length && !contains) {
            if (ObjectUtil.equals(array[i], toSearch)) {
               contains = true;
            }
            i++;
         }
      }
      return contains;
   }
}
