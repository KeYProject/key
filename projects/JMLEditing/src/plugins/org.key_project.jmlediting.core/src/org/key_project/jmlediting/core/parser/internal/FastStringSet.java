package org.key_project.jmlediting.core.parser.internal;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.key_project.jmlediting.core.parser.IFastStringSet;

public class FastStringSet implements IFastStringSet {

   /**
    * The minimum start character of all strings in the set.
    */
   private final int minStartCharacter;
   /**
    * The maximum start character of all strings int the set.
    */
   private final int maxStartCharacter;

   /**
    * The set entries: all possible begin characters x maximum length of string
    * contained for that begin character x all strings for that length and begin
    * character. A String with begin character c and length l is contained in
    * the array at setEntries[c - minStartCharacter - Character.MIN_VALUE][l].
    */
   private final String[][][] setEntries;

   /**
    * A {@link Comparator} to compare strings only by length.
    */
   private static Comparator<String> lengthComparator = new Comparator<String>() {

      @Override
      public int compare(final String arg0, final String arg1) {
         return arg0.length() - arg1.length();
      }
   };

   /**
    * Creates a new {@link FastStringSet} with the given Strings.
    *
    * @param entries
    *           all strings to be contained in the set
    */
   public FastStringSet(final String... entries) {
      // We want to fill setEntries as specified in its comment

      // First sort all strings to have them sorted by first letter
      final ArrayList<String> sortedEntries = new ArrayList<String>(
            entries.length);
      sortedEntries.addAll(Arrays.asList(entries));

      Collections.sort(sortedEntries);

      // Find lower and upper bounds for start and end character and create the
      // setEntries array

      this.minStartCharacter = sortedEntries.get(0).charAt(0);
      this.maxStartCharacter = sortedEntries.get(sortedEntries.size() - 1)
            .charAt(0);

      this.setEntries = new String[this.maxStartCharacter
            - this.minStartCharacter + 1][][];

      // Then iterate to all possible first characters and find the string which
      // start with it
      // Because the list is sorted, this works in O(numCharacters + numStrings)
      int listIndex = 0;
      for (int beginChar = this.minStartCharacter; beginChar <= this.maxStartCharacter; beginChar++) {
         final int listBeginIndex = listIndex;
         int maxLength = 0;

         // Go further in the list of strings as long as string which the
         // startCharacter are found
         // While iterating through the list find the length of the string with
         // maximum length
         while (listIndex < sortedEntries.size()
               && sortedEntries.get(listIndex).charAt(0) == (char) beginChar) {
            maxLength = Math.max(maxLength, sortedEntries.get(listIndex)
                  .length());
            listIndex++;
         }

         // Now place them in the allEntries array
         if (listIndex == listBeginIndex) {
            // No strings start with beginChar
            this.setEntries[beginChar - this.minStartCharacter
                  - Character.MIN_VALUE] = new String[0][0];
         }
         else {
            // Create the array for the length; length needs to be a valid index
            this.setEntries[beginChar - this.minStartCharacter
                  - Character.MIN_VALUE] = new String[maxLength + 1][];

            // Sort the string by length
            final List<String> sortedLength = new ArrayList<String>(listIndex
                  - listBeginIndex);
            sortedLength.addAll(sortedEntries
                  .subList(listBeginIndex, listIndex));
            Collections.sort(sortedLength, lengthComparator);

            // Now do the same thing as with the start characters but with the
            // length
            // Find all for all possible length all string with that length
            int lengthIndex = 0;
            for (int length = 0; length <= maxLength; length++) {
               final int lengthBeginIndex = lengthIndex;
               while (lengthIndex < sortedLength.size()
                     && sortedLength.get(lengthIndex).length() == length) {
                  lengthIndex++;
               }

               if (lengthIndex == lengthBeginIndex) {
                  // No entries with this length
                  this.setEntries[beginChar - this.minStartCharacter
                        - Character.MIN_VALUE][length] = new String[0];
               }
               else {
                  // Place all strings with that length in the array
                  // If that number is small, we can check very efficiently,
                  // whether to string is in the set
                  this.setEntries[beginChar - this.minStartCharacter
                        - Character.MIN_VALUE][length] = sortedLength.subList(
                        lengthBeginIndex, lengthIndex).toArray(
                        new String[lengthIndex - lengthBeginIndex]);
               }

            }
         }
      }
   }

   @Override
   public boolean contains(final String s) {
      final char beginChar = s.charAt(0);
      // Check whether the first char can be in the set
      if (beginChar < this.minStartCharacter
            || beginChar > this.maxStartCharacter) {
         return false;
      }

      // Get all strings with the first char
      final String[][] stringBeginWithChar = this.setEntries[beginChar
            - this.minStartCharacter - Character.MIN_VALUE];

      // Then check whether the given length is possible
      final int length = s.length();
      if (stringBeginWithChar.length <= length) {
         return false;
      }
      // Find all strings with that length
      final String[] stringsWithLength = stringBeginWithChar[length];
      if (stringsWithLength.length == 0) {
         return false;
      }
      // If there are strings, no look whether the string is contained
      // It is assumed to have here not more than two or tree strings, so the
      // loop is fast
      for (final String entry : stringsWithLength) {
         if (s.equals(entry)) {
            return true;
         }
      }
      return false;
   }

}
