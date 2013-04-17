// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Collection;
import java.util.Iterator;
import java.util.StringTokenizer;

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
    * Adds all elements to the {@link Collection}. 
    * @param <T> The type of the {@link Collection}s elements.
    * @param collection The {@link Collection} to add to.
    * @param elementsToAdd The elements to add.
    */
   public static <T> void addAll(Collection<T> collection, T... elementsToAdd) {
      if (collection != null && elementsToAdd != null) {
         for (T toAdd : elementsToAdd) {
            collection.add(toAdd);
         }
      }
   }
   
   /**
    * Returns the index of the element to search in the given iterator.
    * @param iter The iterator to search in.
    * @param toSearch The element to search.
    * @return The index of the element or {@code -1} if it was not found.
    */
   public static <T> int indexOf(Iterator<T> iter, T toSearch) {
      if (iter != null) {
         int i = 0;
         boolean found = false;
         while (!found && iter.hasNext()) {
            T next = iter.next();
            if (next != null ? next.equals(toSearch) : toSearch == null) {
               found = true;
            }
            else {
               i++;
            }
         }
         if (found) {
            return i;
         }
         else {
            return -1;
         }
      }
      else {
         return -1;
      }
   }
   
   /**
    * Returns the index of the element to search in the given array.
    * @param array The array to search in.
    * @param toSearch The element to search.
    * @return The index of the element or {@code -1} if it was not found.
    */
   public static <T> int indexOf(T[] array, T toSearch) {
      int index = -1;
      if (array != null) {
         int i = 0;
         while (i < array.length && index < 0) {
            if (array[i] != null ? array[i].equals(toSearch) : toSearch == null) {
               index = i;
            }
            i++;
         }
      }
      return index;
   }
   
   /**
    * Creates a line which consists of the given text.
    * @param text The text to repeate.
    * @param repetitions The number of repetitions.
    * @return The created line.
    */
   public static String createLine(String text, int repetitions) {
      StringBuffer sb = new StringBuffer();
      for (int i = 0; i < repetitions; i++) {
         sb.append(text);
      }
      return sb.toString();
   }
   
   /**
    * <p>
    * Encodes the given text in a way that it contains no XML elements
    * and can be used for instance as plain text or attribute value.
    * </p>
    * <p>
    * The following signs are replaced:
    * <pre>
    * " => &quot;quot;
    * & => &quot;amp;
    * ' => &quot;apos;
    * < => &quot;lt;
    * > => &quot;gt;
    * </pre>
    * </p>
    * @param text The text to encode.
    * @return The encoded text.
    */
   public static String encodeText(String text) {
      if (text != null) {
         char[] signs = text.toCharArray();
         StringBuffer sb = new StringBuffer();
         for (char sign : signs) {
            switch (sign) {
               case '"' : sb.append("&quot;");
                          break;
               case '&' : sb.append("&amp;");
                          break;
               case '\'' : sb.append("&apos;");
                           break;
               case '<' : sb.append("&lt;");
                          break;
               case '>' : sb.append("&gt;");
                          break;
               default : sb.append(sign);
                         break;
            }
         }
         return sb.toString();
      }
      else {
         return null;
      }
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

   /**
    * Searches an element in the given {@link Iterable} instance and removes
    * the found element from it.
    * @param iterable The instance to search in.
    * @param filter The filter to select an element.
    * @return The found element or {@code null} if no element was found.
    */
   public static <T> T searchAndRemove(Iterable<T> iterable, IFilter<T> filter) {
      T result = null;
      if (iterable != null && filter != null) {
         Iterator<T> iter = iterable.iterator();
         if (iter != null) {
            while (result == null && iter.hasNext()) {
               T next = iter.next();
               if (filter.select(next)) {
                  result = next;
                  iter.remove();
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Checks the equality of the given {@link String}s ignoring whitespace.
    * @param first The first {@link String}.
    * @param second The second {@link String}.
    * @return {@code true} equal ignoring whitespace, {@code false} different.
    */
   public static boolean equalIgnoreWhiteSpace(String first, String second) {
      if (first != null) {
         if (second != null) {
            StringTokenizer firstTokenizer = new StringTokenizer(first);
            StringTokenizer secondTokenizer = new StringTokenizer(second);
            boolean equal = true;
            while (equal && firstTokenizer.hasMoreTokens() && secondTokenizer.hasMoreTokens()) {
               String firstNext = firstTokenizer.nextToken();
               String secondNext = secondTokenizer.nextToken();
               equal = firstNext.equals(secondNext);
            }
            return equal && !firstTokenizer.hasMoreElements() && !secondTokenizer.hasMoreElements();
         }
         else {
            return false;
         }
      }
      else {
         return second == null;
      }
   }
}