package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Collection;
import java.util.Iterator;

/**
 * Provides static utitlity methods for Java in general like
 * {@link Object}s, {@link String}s, array or {@link Collection}s.
 * @author Martin Hentschel
 */
public final class JavaUtil {
   /**
    * Forbid instances.
    */
   private JavaUtil() {
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
    * Checks if the trimmed {@link String} is empty.
    * @param text The text to check.
    * @return {@code true} = text is {@code null} or trimmed empty, {@code false} = text is not empty.
    */
   public static boolean isTrimmedEmpty(String text) {
      return text == null || text.trim().isEmpty();
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
    * Counts the number of elements in the given {@link Iterable} which
    * are selected by the given {@link IFilter}.
    * @param iterable The elements to count in.
    * @param filter The {@link IFilter} to select elements.
    * @return The number of elements selected by the {@link IFilter} in the given {@link Iterable}.
    */
   public static <T> int count(Iterable<T> iterable, IFilter<T> filter) {
      int count = 0;
      if (iterable != null && filter != null) {
         for (T element : iterable) {
            if (filter.select(element)) {
               count ++;
            }
         }
      }
      return count;
   }
   
   /**
    * Searches an element in the given {@link Iterable} instance.
    * @param iterable The instance to search in.
    * @param filter The filter to select an element.
    * @return The found element or {@code null} if no element was found.
    */
   public static <T> T search(Iterable<T> iterable, IFilter<T> filter) {
      T result = null;
      if (iterable != null && filter != null) {
         Iterator<T> iter = iterable.iterator();
         if (iter != null) {
            while (result == null && iter.hasNext()) {
               T next = iter.next();
               if (filter.select(next)) {
                  result = next;
               }
            }
         }
      }
      return result;
   }   
   
}
