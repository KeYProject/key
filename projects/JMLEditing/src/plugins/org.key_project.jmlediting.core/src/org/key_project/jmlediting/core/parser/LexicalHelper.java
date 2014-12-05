package org.key_project.jmlediting.core.parser;

import static org.key_project.jmlediting.core.parser.ParserUtils.validatePositions;

/**
 * This class provides some utility functions for lexing.
 *
 * @author Moritz Lichter
 *
 */
public final class LexicalHelper {

   /**
    * No instantiations.
    */
   private LexicalHelper() {

   }

   /**
    * Scans the text from the start index on for a closing semicolon. Semicolons
    * in strings or chars are ignored.
    *
    * @param text
    *           the test to scan in
    * @param start
    *           the start position of scanning
    * @param end
    *           the maximum position
    * @return the position of the next closing semicolon
    * @throws ParserException
    *            if no semicolon is found
    */
   public static int scanForClosingSemicolon(final String text,
         final int start, final int end) throws ParserException {
      boolean isStringOrChar = false;
      char quoteChar = ' ';
      int position = start;
      while (position < end) {
         final char c = text.charAt(position);
         final boolean isQuoteChar = c == '\'' || c == '\"';
         if (isQuoteChar && !isStringOrChar) {
            isStringOrChar = true;
            quoteChar = c;
         }
         else if (isStringOrChar) {
            if (c == '\\') {
               // now escaping a character in a string
               // this is not a ; to search for
               position = position + 2;
               // dont look at the next one
               continue;
            }
            else {
               if (c == quoteChar) {
                  // close string or char
                  isStringOrChar = false;
                  quoteChar = ' ';
               }
            }
         }
         if (!isStringOrChar) {
            if (c == ';') {
               break;
            }
         }
         position++;
      }
      if (position >= end) {
         throw new ParserException("No closing semicolon found", text, end);
      }
      return position;

   }

   /**
    * Returns an identifier starting at the given position.
    *
    * @param text
    *           the text to search into
    * @param start
    *           the begin index of the identifier
    * @param end
    *           the maximum position
    * @return the index of the next character after the identifier
    * @throws ParserException
    *            no identifier is found
    */
   public static int getIdentifier(final String text, final int start,
         final int end) throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      if (start == end) {
         throw new ParserException("Expected an identifier", text, start);
      }
      if (!Character.isJavaIdentifierStart(text.charAt(position))) {
         throw new ParserException("Not a valid Java identifier", text,
               position);
      }
      position++;
      while (position < end
            && Character.isJavaIdentifierPart(text.charAt(position))) {
         position++;
      }
      return position;
   }

   /**
    * Skips the following whitespaces and @ signs, if a new line is encountered.
    *
    * @param text
    *           the text to skip in
    * @param start
    *           the start position of skipping
    * @param end
    *           the maximum (exclusive) position
    * @return the index of the first not skipped character
    * @throws ParserException
    *            invalid indices
    */
   public static int skipWhiteSpacesOrAt(final String text, final int start,
         final int end, final boolean beginAtNewLine) throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      boolean inNewLine = beginAtNewLine;
      while (position < end
            && ((inNewLine && text.charAt(position) == '@') || Character
                  .isWhitespace(text.charAt(position)))) {
         if (text.charAt(position) == '\n') {
            inNewLine = true;
         }
         position++;
      }
      return position;
   }

   /**
    * Skips the following whitespaces.
    *
    * @param text
    *           the text to skip in
    * @param start
    *           the start position of skipping
    * @param end
    *           the maximum (exclusive) position
    * @return the index of the first not skipped character
    * @throws ParserException
    *            invalid indices
    */
   public static int skipWhiteSpaces(final String text, final int start,
         final int end) throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      while (position < end && Character.isWhitespace(text.charAt(position))) {
         position++;
      }
      return position;
   }

}
