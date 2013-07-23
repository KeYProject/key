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

import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

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
    * Searches an element in the given {@link Iterable} instance.
    * @param array The instance to search in.
    * @param filter The filter to select an element.
    * @return The found element or {@code null} if no element was found.
    */
   public static <T> T search(T[] array, IFilter<T> filter) {
      T result = null;
      if (array != null && filter != null) {
         int i = 0;
         while (result == null && i < array.length) {
            if (filter.select(array[i])) {
               result = array[i];
            }
            i++;
         }
      }
      return result;
   }
   
   /**
    * <p>
    * Adds the given elements to the existing array. The result is a new
    * array that contains the other elements in the end.
    * </p>
    * <p>
    * <b>Attention: </b> It is not possible to use this method with
    * two {@code null} parameters. In this case is an {@link IllegalArgumentException}
    * thrown.
    * </p>
    * @param array The array to add to.
    * @param toAdd The elements to add.
    * @return The new created array.
    * @throws IllegalArgumentException Both parameters are {@code null}.
    */
   @SuppressWarnings("unchecked")
   public static <T> T[] addAll(T[] array, T[] toAdd) {
       if (array != null) {
           if (toAdd != null) {
               T[] result = (T[])java.lang.reflect.Array.newInstance(array.getClass().getComponentType(), array.length + toAdd.length);
               System.arraycopy(array, 0, result, 0, array.length);
               System.arraycopy(toAdd, 0, result, array.length, toAdd.length);
               return result;
           }
           else {
               T[] result = (T[])java.lang.reflect.Array.newInstance(array.getClass().getComponentType(), array.length);
               System.arraycopy(array, 0, result, 0, array.length);
               return result;
           }
       }
       else {
           if (toAdd != null) {
               T[] result = (T[])java.lang.reflect.Array.newInstance(toAdd.getClass().getComponentType(), toAdd.length);
               System.arraycopy(toAdd, 0, result, 0, toAdd.length);
               return result;
           }
           else {
               throw new IllegalArgumentException("Can not create an array if both paramters are null.");
           }
       }
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
    * @param toAdd The element to add.
    * @return The new created array with one more element.
    * @throws IllegalArgumentException Both parameters are {@code null}.
    */
   @SuppressWarnings("unchecked")
   public static <T> T[] add(T[] array, T toAdd) {
       if (array != null) {
           T[] result = (T[])java.lang.reflect.Array.newInstance(array.getClass().getComponentType(), array.length + 1);
           System.arraycopy(array, 0, result, 0, array.length);
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
    * <p>
    * Adds the given element to the existing array. The result is a new
    * array that contains one more element.
    * </p>
    * @param array The array to extend.
    * @param toAdd The element to add.
    * @return The new created array with one more element.
    */
   public static int[] add(int[] array, int toAdd) {
       if (array != null) {
           int[] result = new int[array.length + 1];
           System.arraycopy(array, 0, result, 0, array.length);
           result[array.length] = toAdd;
           return result;
       }
       else {
           return new int[] {toAdd};
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
      return contains(array, toSearch, ObjectUtil.createEqualsComparator());
   }

   /**
    * Checks if the given array contains the element to search. The equality is
    * computed via the comparator. Objects are equal if the comparison result is {@code 0}.
    * @param <T> The type of the array.
    * @param array The array.
    * @param toSearch The element to search.
    * @param comparator the {@link Comparator} to use.
    * @return {@code true} if the array contains the element or {@code false} if not or if the array is {@code null}.
    * @throws IllegalArgumentException If the comparator is {@code null}.
    */
   public static <T> boolean contains(T[] array, T toSearch, Comparator<T> comparator) {
      return indexOf(array, toSearch, comparator) >= 0;
   }

   /**
    * Returns the first index in the given array that contains the
    * element to search.
    * @param array The array to search in.
    * @param toSearch The element to search.
    * @return The first index in the array that contains the element to search or {@code -1} if the elment is not containd in the array.
    */
   public static <T> int indexOf(T[] array, T toSearch) {
      return indexOf(array, toSearch, ObjectUtil.createEqualsComparator());
   }
   
   /**
    * Returns the first index in the given array that contains the
    * element to search. The equality is
    * computed via the comparator. Objects are equal if the comparison result is {@code 0}.
    * @param array The array to search in.
    * @param toSearch The element to search.
    * @param comparator the {@link Comparator} to use.
    * @return The first index in the array that contains the element to search or {@code -1} if the elment is not containd in the array.
    * @throws IllegalArgumentException If the comparator is {@code null}.
    */
   public static <T> int indexOf(T[] array, T toSearch, Comparator<T> comparator) {
      int index = -1;
      if (array != null) {
         if (comparator == null) {
            throw new IllegalArgumentException("Comparator is null.");
         }
         else {
            int i = 0;
            while (i < array.length && index < 0) {
               if (comparator.compare(array[i], toSearch) == 0) {
                  index = i;
               }
               i++;
            }
         }
      }
      return index;
   }

   /**
    * Removes all occurrences from toRemove in the array. The equality is
    * computed via {@link ObjectUtil#equals(Object, Object)}.
    * @param array The array to remove from.
    * @param toRemove The element to remove.
    * @return A copy of the array without the element toRemove or {@code null} if the given array was {@code null}.
    */
   public static <T> T[] remove(T[] array, T toRemove) {
       return remove(array, toRemove, ObjectUtil.<T>createEqualsComparator());
   }
   
   /**
    * Removes all occurrences from toRemove in the array. The equality is
    * computed via the comparator. Objects are equal if the comparison result is {@code 0}.
    * @param array The array to remove from.
    * @param toRemove The element to remove.
    * @param comparator The {@link Comparator} to use.
    * @return A copy of the array without the element toRemove or {@code null} if the given array was {@code null}.
    * @throws IllegalArgumentException If the comparator is {@code null}.
    */
   @SuppressWarnings("unchecked")
   public static <T> T[] remove(T[] array, T toRemove, Comparator<T> comparator) {
      if (array != null) {
         if (comparator == null) {
            throw new IllegalArgumentException("Comparator is null.");
         }
         else {
            List<T> result = new LinkedList<T>();
            if (array != null) {
               for (T element : array) {
                  if (comparator.compare(element, toRemove) != 0) {
                     result.add(element);
                  }
               }
            }
            return result.toArray((T[])java.lang.reflect.Array.newInstance(array.getClass().getComponentType(), result.size()));
         }
      }
      else {
         return null;
      }
   }

   /**
    * Converts the given array into a {@link String}.
    * For each element is {@link ObjectUtil#toString()} used to convert it
    * into a {@link String}.
    * @param array The array to convert.
    * @return The array as {@link String}.
    */
   public static <T> String toString(T[] array) {
       return toString(array, ", ");
   }
   
   /**
    * Converts the given array into a {@link String}.
    * For each element is {@link ObjectUtil#toString()} used to convert it
    * into a {@link String}.
    * @param array The array to convert.
    * @param separator The separator between to array elements.
    * @return The array as {@link String}.
    */
   public static <T> String toString(T[] array, String separator) {
       StringBuffer sb = new StringBuffer();
       if (array != null) {
           boolean afterFirst = false;
           for (T element : array) {
               if (afterFirst) {
                   sb.append(separator);
               }
               else {
                   afterFirst = true;
               }
               sb.append(ObjectUtil.toString(element));
           }
       }
       return sb.toString();
   }

   /**
    * Converts the given array into a {@link String}.
    * @param array The array to convert.
    * @return The array as {@link String}.
    */
   public static String toString(int[] array) {
       return toString(array, ", ");
   }
   
   /**
    * Converts the given array into a {@link String}.
    * @param array The array to convert.
    * @param separator The separator between to array elements.
    * @return The array as {@link String}.
    */
   public static String toString(int[] array, String separator) {
       StringBuffer sb = new StringBuffer();
       if (array != null) {
           boolean afterFirst = false;
           for (int element : array) {
               if (afterFirst) {
                   sb.append(separator);
               }
               else {
                   afterFirst = true;
               }
               sb.append(ObjectUtil.toString(element));
           }
       }
       return sb.toString();
   }

   /**
    * Checks if the given array is empty.
    * @param array The array to check.
    * @return {@code true} array is empty or {@code null}, {@code false} array is not empty.
    */
   public static <T> boolean isEmpty(T[] array) {
      return array == null || array.length == 0;
   }

   /**
    * Returns the previous element if available from the array.
    * @param array The array to search in.
    * @param toSearch The element for that the previous one is needed.
    * @return The previous element or {@code null} if no element was found.
    */
   public static <T> T getPrevious(T[] array, T toSearch) {
      return getPrevious(array, toSearch, ObjectUtil.<T>createEqualsComparator());
   }

   /**
    * Returns the previous element if available from the array. The equality is
    * computed via the comparator. Objects are equal if the comparison result is {@code 0}.
    * @param array The array to search in.
    * @param toSearch The element for that the previous one is needed.
    * @param comparator the {@link Comparator} to use.
    * @return The previous element or {@code null} if no element was found.
    * @throws IllegalArgumentException If the comparator is {@code null}.
    */
   public static <T> T getPrevious(T[] array, T toSearch, Comparator<T> comparator) throws IllegalArgumentException {
      int index = indexOf(array, toSearch, comparator);
      if (index >= 1) {
         return array[index - 1];
      }
      else {
         return null;
      }
   }

   /**
    * Checks if the given element is the last element in the array.
    * @param <T> The type of the array.
    * @param array The array.
    * @param toSearch The element to search.
    * @return {@code true} is last element, {@code false} is not last element or even not contained in the array.
    */
   public static <T> boolean isLast(T[] array, T toSearch) {
      return isLast(array, toSearch, ObjectUtil.createEqualsComparator());
   }

   /**
    * Checks if the given element is the last element in the array.
    * Objects are equal if the comparison result is {@code 0}.
    * @param <T> The type of the array.
    * @param array The array.
    * @param toSearch The element to search.
    * @param comparator the {@link Comparator} to use.
    * @return {@code true} is last element, {@code false} is not last element or even not contained in the array.
    * @throws IllegalArgumentException If the comparator is {@code null}.
    */
   public static <T> boolean isLast(T[] array, T toSearch, Comparator<T> comparator) {
      if (array != null && array.length >= 1) {
         if (comparator == null) {
            throw new IllegalArgumentException("Comparator is null.");
         }
         else {
            return comparator.compare(array[array.length - 1], toSearch) == 0;
         }
      }
      else {
         return false;
      }
   }
   
   /**
    * Returns the first element from the given array.
    * @param array The array to get first element from.
    * @return The first element or {@code null} if no element is available.
    */
   public static <T> T getFirst(T[] array) {
      if (!isEmpty(array)) {
         return array[0];
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the last element from the given array.
    * @param array The array to get last element from.
    * @return The first element or {@code null} if no element is available.
    */
   public static <T> T getLast(T[] array) {
      if (!isEmpty(array)) {
         return array[array.length - 1];
      }
      else {
         return null;
      }
   }
}