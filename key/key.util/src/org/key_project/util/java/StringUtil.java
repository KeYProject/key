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

package org.key_project.util.java;

import java.util.Arrays;
import java.util.Comparator;

import javax.swing.JFileChooser;

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
    * The latin alphabet with big capitals.
    */
   public static final String LATIN_ALPHABET_BIG = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
   
   /**
    * The latin alphabet with small capitals.
    */
   public static final String LATIN_ALPHABET_SMALL = LATIN_ALPHABET_BIG.toLowerCase();
   
   /**
    * Additional characters allowed in file systems.
    * <p>
    * It is important that {@code ':'} is not contained because {@code "::"} is replaced with a {@code '/'} by the {@link JFileChooser} under Mac OS.
    */
   public static final char[] ADDITIONAL_ALLOWED_FILE_NAME_SYSTEM_CHARACTERS = {'(', ')', '[', ']', '-', '+', '_', '$', ',', '%'};
 
   /**
    * The numerals.
    */
   public static final String NUMERALS = "0123456789";
   
   /**
    * All characters representing whitespace.
    */
   public static final String WHITESPACE = " \n\r\t";
   
   /**
    * Static constructor.
    */
   static {
      Arrays.sort(ADDITIONAL_ALLOWED_FILE_NAME_SYSTEM_CHARACTERS);
   }
   
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
            char[] firstContent = first.toCharArray();
            char[] secondContent = second.toCharArray();
            int firstIndex = 0;
            int secondIndex = 0;
            // Skip initial whitespace
            while (firstIndex < firstContent.length &&
                   contains(WHITESPACE, firstContent[firstIndex] + EMPTY_STRING)) {
               firstIndex++;
            }
            while (secondIndex < secondContent.length &&
                   contains(WHITESPACE, secondContent[secondIndex] + EMPTY_STRING)) {
               secondIndex++;
            }
            // Start to compare content
            boolean equal = true;
            while (equal && firstIndex < firstContent.length && secondIndex < secondContent.length) {
               // Compare content
               if (firstIndex < firstContent.length && secondIndex < secondContent.length) {
                  if (firstContent[firstIndex] != secondContent[secondIndex]) {
                     equal = false;
                  }
               }
               else {
                  if (firstIndex < firstContent.length - 1 || secondIndex < secondContent.length - 1) {
                     equal = false;
                  }
               }
               firstIndex++;
               secondIndex++;
               // Skip whitespace
               while (firstIndex < firstContent.length &&
                      contains(WHITESPACE, firstContent[firstIndex] + EMPTY_STRING)) {
                  firstIndex++;
               }
               while (secondIndex < secondContent.length &&
                      contains(WHITESPACE, secondContent[secondIndex] + EMPTY_STRING)) {
                  secondIndex++;
               }
            }
            return equal &&
                   firstIndex >= firstContent.length && secondIndex >= secondContent.length; // Complete content of both texts compared
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
    * Fills the given text with the leading character until it has the defined length.
    * @param text The text to fill.
    * @param leadingCharacter The leading character to use.
    * @param length The length to fill up to.
    * @return The created text.
    * @throws IllegalArgumentException If the text is already longer as the given length
    */
   public static String fillString(String text, char leadingCharacter, int length) throws IllegalArgumentException {
      StringBuffer sb = new StringBuffer();
      if (text != null) {
         if (text.length() > length) {
            throw new IllegalArgumentException("Text \"" + text + "\" with length " + text.length() + " is longer as " + length + ".");
         }
         else {
            for (int i = 0; i < length - text.length(); i++) {
               sb.append(leadingCharacter);
            }
            sb.append(text);
         }
      }
      else {
         for (int i = 0; i < length; i++) {
            sb.append(leadingCharacter);
         }
      }
      return sb.toString();
   }

   /**
    * Performs a trim only on the right side.
    * @param text The text to trim its right side.
    * @return The trimmed text.
    */
   public static String trimRight(String text) {
      if (text != null) {
         char[] content = text.toCharArray();
         int newLength = content.length;
         while (newLength >= 1 && Character.isWhitespace(content[newLength - 1])) {
            newLength--;
         }
         return newLength == text.length() ? text : text.substring(0, newLength);
      }
      else {
         return null;
      }
   }

   /**
    * Chops the given text if required.
    * @param text The text to check.
    * @param maxLength The maximal length to ensure.
    * @return The text considering the maximal length.
    */
   public static String chop(String text, int maxLength) {
      if (text != null && text.length() > maxLength) {
         if (maxLength <= 0) {
            return EMPTY_STRING;
         }
         else if (maxLength == 1) {
            return ".";
         }
         else if (maxLength == 2) {
            return "..";
         }
         else if (maxLength == 3) {
            return "...";
         }
         else {
            return text.substring(0, maxLength - 3) + "...";
         }
      }
      else {
         return text;
      }
   }
}