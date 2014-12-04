package org.key_project.jmlediting.core.parser;

/**
 * Provides some utility functions for parsing.
 *
 * @author Moritz Lichter
 *
 */
public final class ParserUtils {

   /**
    * No instantiations.
    */
   private ParserUtils() {

   }

   /**
    * Validates the start and end position for a given text.
    *
    * @param text
    *           the text
    * @param start
    *           the start position (inclusive)
    * @param end
    *           the end position (exclusive)
    * @throws ParserException
    *            when the positions are invalid
    */
   public static void validatePositions(final String text, final int start,
         final int end) throws ParserException {
      if (start < 0) {
         throw new ParserException("Given start index is out of bounds: "
               + start + " < 0", text, start);
      }
      if (start >= text.length()) {
         throw new ParserException("Given start index is out of bounds: "
               + start + " >= " + text.length(), text, start);
      }
      if (end < start) {
         throw new ParserException("start < end", text, start);
      }
      if (end > text.length()) {
         throw new ParserException("Given end index is out of bounds: " + end
               + " >= " + text.length(), text, end);
      }
   }

}
