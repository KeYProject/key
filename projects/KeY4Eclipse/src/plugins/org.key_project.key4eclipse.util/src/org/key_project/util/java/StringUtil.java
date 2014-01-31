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

import java.util.Arrays;
import java.util.Comparator;
import java.util.StringTokenizer;

/**
 * Provides static methods to work with strings.
 * @author Martin Hentschel
 */
public final class StringUtil {
   /**
    * Constant for an empty string.
    */
   public static final String EMPTY_STRING = "";

   /**
    * Constant for a line break.
    */
   public static final String NEW_LINE = System.getProperty("line.separator");
   
   /**
    * Forbid instances by this private constructor.
    */
   private StringUtil() {
   }
   
   /**
    * Checks if the {@link String} is empty.
    * @param text The text to check.
    * @return {@code true} = text is {@code null} or empty, {@code false} = text is not empty.
    */
   public static boolean isEmpty(String text) {
      return text == null || text.isEmpty();
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
    * Nullpointer save execution of {@link String#trim()}
    * @param text The text.
    * @return The trimmed text.
    */
   public static String trim(String text) {
      return text != null ? text.trim() : null;
   }

   /**
    * Nullpointer save execution of {@link String#toLowerCase()}.
    * @param text The text to convert.
    * @return The text in lower case or {@code null} if the given text is {@code null}.
    */
   public static String toLowerCase(String text) {
       return text != null ? text.toLowerCase() : null;
   }
   
   /**
    * Creates a {@link Comparator} that can be used to compute the
    * equality of two given {@link String}s ignoring the case
    * via {@link String#compareToIgnoreCase(String)}. If both values
    * are {@code null} also {@code 0} is returned in 
    * {@link Comparator#compare(Object, Object)}. If only one value
    * is {@code null} {@link Comparator#compare(Object, Object)} will
    * return a value different to {@code 0}.
    * @return The created {@link Comparator}.
    */
   public static Comparator<String> createIgnoreCaseComparator() {
      return new Comparator<String>() {
         @Override
         public int compare(String o1, String o2) {
            if (o1 != null && o2 != null) {
               return o1.compareToIgnoreCase(o2);
            }
            else {
               return o1 == null && o2 == null ? 0 : 1;
            }
         }
      };
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
    * Checks if the given string contains the substring.
    * </p>
    * <p>
    * <b>Attention:</b> The empty string is contained in every string. 
    * </p>
    * @param string The string that should contain the substring.
    * @param substring The substring to check.
    * @return {@code true} strings are not {@code null} and the string contains the substring, {@code false} if at least one string is {@code null} or the string does not contain the substring.
    */
   public static boolean contains(String string, CharSequence substring) {
      return string != null && substring != null ? string.contains(substring) : false;
   }

   /**
    * Converts the optional multi lined {@link String} in a single lined {@link String}
    * by replacing all line breaks and tabs with a space.
    * @param text The text to convert.
    * @return The single lined text.
    */
   public static String toSingleLinedString(String text) {
      return replaceAll(text, new char[] {'\n', '\r', '\t'}, ' ');
   }

   /**
    * Replaces all occurrences of a search sign with the replacement sign.
    * @param text The text to search and replace in.
    * @param toSearch The signs to search.
    * @param toReplace The sign to replace with.
    * @return The new created {@link String}.
    */
   public static String replaceAll(String text, char[] toSearch, char toReplace) {
      if (text != null && toSearch != null) {
         // Sort toSearch
         Arrays.sort(toSearch);
         // Create new String.
         char[] signs = text.toCharArray();
         for (int i = 0; i < signs.length; i++) {
            int index = Arrays.binarySearch(toSearch, signs[i]);
            if (index >= 0) {
               signs[i] = toReplace;
            }
         }
         return new String(signs);
      }
      else {
         return text;
      }
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