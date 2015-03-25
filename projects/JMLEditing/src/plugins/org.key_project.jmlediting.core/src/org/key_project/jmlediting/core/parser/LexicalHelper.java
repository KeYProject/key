package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.parser.internal.FastStringSet;
import org.key_project.jmlediting.core.parser.internal.ParserUtils;

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
    * Scans the text from the start index on for a closing given character.
    * characters in strings or chars are ignored.
    *
    * @param character
    *           the character to search for
    * @param text
    *           the test to scan in
    * @param start
    *           the start position of scanning
    * @param end
    *           the maximum position
    * @return the position of the next closing character
    * @throws ParserException
    *            if no semicolon is found
    */
   public static int scanForClosingCharacter(final int character,
         final String text, final int start, final int end)
         throws ParserException {
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
            if (c == character) {
               break;
            }
         }
         position++;
      }
      if (position >= end) {
         throw new ParserException("No closing " + character + " found", text,
               end);
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
      ParserUtils.validatePositions(text, start, end);
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
      final String ident = text.substring(start, position);
      if (javaKeywords.contains(ident)) {
         throw new ParserException("Java keyword " + ident
               + " is not allowed as identifier.", text, start);
      }
      return position;
   }

   private static FastStringSet javaKeywords;
   static {
      try {
         javaKeywords = new FastStringSet("abstract", "assert", "boolean",
               "break", "byte", "case", "catch", "char", "class", "const",
               "continue", "default", "do", "double", "else", "extends",
               "false", "final", "finally", "float", "for", "goto", "if",
               "implements", "import", "instanceof", "int", "interface",
               "long", "native", "new", "null", "package", "private",
               "protected", "public", "return", "short", "static", "strictfp",
               "super", "switch", "synchronized", "this", "throw", "throws",
               "transient", "true", "try", "void", "volatile", "while");
      }
      catch (final Exception e) {
         e.printStackTrace();
      }
   }

   public static int getJMLKeywordIdentifier(final String text,
         final int start, final int end) throws ParserException {
      ParserUtils.validatePositions(text, start, end);
      int position = start;
      if (start == end) {
         throw new ParserException("Expected an identifier", text, start);
      }
      if (!(text.charAt(position) == '\\' || Character
            .isJavaIdentifierStart(text.charAt(position)))) {
         throw new ParserException("Not a valid JML keyword identifier begin '"
               + text.charAt(position) + "'", text, position);
      }
      position++;
      while (position < end
            && Character.isJavaIdentifierPart(text.charAt(position))) {
         position++;
      }
      return position;
   }

   public static int getIntegerConstant(final String text, final int start,
         final int end) throws ParserException {
      ParserUtils.validatePositions(text, start, end);
      if (start == end) {
         throw new ParserException("Expected an integer contant", text, start);
      }
      final char firstChar = text.charAt(start);
      int position;
      if (firstChar == '0') {
         if (start + 1 < end) {
            final char secondChar = text.charAt(start + 1);
            if (secondChar == 'x') {
               // Hex integer
               position = start + 2;
               while (position < end) {
                  final char c = text.charAt(position);
                  if (isHexDigit(c)) {
                     position++;
                  }
                  else {
                     break;
                  }
               }
               if (position == start + 2) {
                  // No character after x, invalid
                  throw new ParserException("Got invalid hexadeicmal constant",
                        text, position + 3);
               }
            }
            else {
               // Octal
               position = start + 1;
               while (position < end) {
                  final char c = text.charAt(position);
                  if (isOctalDigit(c)) {
                     position++;
                  }
                  else {
                     break;
                  }
               }
            }
         }
         else {
            // Got a simple literal "0"
            position = start + 1;
         }
      }
      else {
         // Decimal integer
         position = scanDigits(text, start, end);
      }

      if (position == start) {
         throw new ParserException("Expected an integer constant", text, start);
      }

      // check for type suffix
      if (position < end) {
         final char c = text.charAt(position);
         if (c == 'l' || c == 'L') {
            position++;
         }
      }

      return position;

   }

   private static boolean isOctalDigit(final char c) {
      return (c >= '0' && c <= '7');
   }

   private static boolean isHexDigit(final char c) {
      return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'F');
   }

   private static int scanDigits(final String text, final int start,
         final int end) {
      int position = start;
      while (position < end) {
         final char c = text.charAt(position);
         if ((c >= '0' && c <= '9')) {
            position++;
         }
         else {
            break;
         }
      }
      return position;
   }

   /**
    * Scans for a floating point constant at the given start position and
    * returns the end position of the constant. If there is no valid floating
    * point constant a {@link ParserException} is thrown.
    *
    * @param text
    *           the text to scan in
    * @param start
    *           the position where a float constant should be scanned
    * @param end
    *           the maximum position in the text (exclusive)
    * @return the exclusive end index of the scanned float constant
    * @throws ParserException
    *            if no float constant could be scanned
    */
   public static int getFloatConstant(final String text, final int start,
         final int end) throws ParserException {
      ParserUtils.validatePositions(text, start, end);
      if (start == end) {
         throw new ParserException("Expected an float constant", text, start);
      }

      // Scan the numeric part: [digits] . [digits]
      int digitsEnd = scanDigits(text, start, end);
      if (digitsEnd == end) {
         throw new ParserException(
               "Expected an float constant, not an integer", text, start);
      }
      final boolean dotFound = text.charAt(digitsEnd) == '.';
      // Tracks whether something was found which can be used to distinguish the
      // float from an int
      boolean floatTypeFound = dotFound;
      if (dotFound) {
         digitsEnd = scanDigits(text, digitsEnd + 1, end);
         if (digitsEnd == end) {
            return digitsEnd;
         }
         // HACK: here we look further than needed but otherwise we get a
         // problem in the
         // grammar because at this subtle points the JML grammar requires the
         // parser
         // to look in the future
         if (text.charAt(digitsEnd) == '.') {
            throw new ParserException("Float contains two dots", text,
                  digitsEnd);
         }
      }
      // At least one digit needs to be scanned
      if (digitsEnd == start) {
         throw new ParserException(
               "Need at least one digits for a float literal", text, start);
      }
      int exponentEnd;
      // Check exponent part
      switch (text.charAt(digitsEnd)) {
      case 'e':
      case 'E':
         int expBeginPos = digitsEnd + 1;
         if (expBeginPos >= end) {
            throw new ParserException("Expected an exponent value", text,
                  expBeginPos);
         }
         // Skip a sign
         final char maybeSignChar = text.charAt(expBeginPos);
         if (maybeSignChar == '-' || maybeSignChar == '+') {
            expBeginPos++;
            if (expBeginPos >= end) {
               throw new ParserException("Expected an exponent value", text,
                     expBeginPos);
            }
         }
         // Get an integer
         exponentEnd = getIntegerConstant(text, expBeginPos, end);
         floatTypeFound = true;
         break;
      default:
         // No exponent
         exponentEnd = digitsEnd;
      }

      if (exponentEnd == end) {
         return exponentEnd;
      }

      // Check float type suffix
      switch (text.charAt(exponentEnd)) {
      case 'f':
      case 'F':
      case 'd':
      case 'D':
         floatTypeFound = true;
         return exponentEnd + 1;
      default:
         if (floatTypeFound) {
            return exponentEnd;
         }
         else {
            throw new ParserException("Got an integer literal", text,
                  exponentEnd);
         }
      }
   }

   /**
    * Scans for a character constant in the given text and the start position.
    *
    * @param text
    *           the text to scan in
    * @param start
    *           the start position
    * @param end
    *           the maximum scan position (exclusive)
    * @return the exclusive end index of the constant
    * @throws ParserException
    *            if no character constant could be scanned
    */
   public static int getCharacterConstant(final String text, final int start,
         final int end) throws ParserException {
      ParserUtils.validatePositions(text, start, end);
      // A character constant needs at least three characters;
      final int minNumChars = 3;
      if (end - start < minNumChars) {
         throw new ParserException("Expected an character constant", text,
               start);
      }
      // Check starting '
      if (text.charAt(start) != '\'') {
         throw new ParserException("Expected a \'", text, start);
      }
      final char character = text.charAt(start + 1);
      int contentEnd;
      // Check the content
      switch (character) {
      case '\\':
         contentEnd = getEscapeSequence(text, start + 1, end);
         break;
      case '\r':
      case '\n':
         throw new ParserException("Illegal escaped character", text, start + 1);
      default:
         contentEnd = start + 2;
      }
      // Check for closing '
      if (contentEnd >= end) {
         throw new ParserException("Expected closing \'", text, contentEnd);
      }
      if (text.charAt(contentEnd) != '\'') {
         throw new ParserException("Expected closing \'", text, contentEnd);
      }
      return contentEnd + 1;

   }

   /**
    * Scans for a string constant in the given text and the start position.
    *
    * @param text
    *           the text to scan in
    * @param start
    *           the start position
    * @param end
    *           the maximum scan position (exclusive)
    * @return the exclusive end index of the constant
    * @throws ParserException
    *            if no string constant could be scanned
    */
   public static int getStringConstant(final String text, final int start,
         final int end) throws ParserException {
      ParserUtils.validatePositions(text, start, end);
      // Need at least two characters for "
      if (end - start < 2) {
         throw new ParserException("Expected a string constant", text, start);
      }

      if (text.charAt(start) != '\"') {
         throw new ParserException("Expected a \"", text, start);
      }
      // Check for characters in the string
      int position = start + 1;
      while (position < end) {
         final char c = text.charAt(position);
         switch (c) {
         case '\"':
            return position + 1;
         case '\\':
            position = getEscapeSequence(text, position, end);
            break;
         case '\r':
         case '\n':
            throw new ParserException("Illegal new line in string", text,
                  position);
         default:
            position++;
         }
      }
      // If the string is valid, the while loop has been exited with the return
      throw new ParserException("Unclosed String", text, position);

   }

   /**
    * Scans for a character escape sequence at pos until end.
    *
    * @param text
    *           the text to scan
    * @param pos
    *           the position to start at
    * @param end
    *           the maximum position (exclusive)
    * @return the exclusive end index of the escape sequence
    * @throws ParserException
    *            if no escape sequence if found
    */
   private static int getEscapeSequence(final String text, final int pos,
         final int end) throws ParserException {
      /**
       * escape-sequence ::= \b // backspace<br>
       * | \t // tab<br>
       * | \n // newline<br>
       * | \r // carriage return<br>
       * | \' // single quote<br>
       * | \" // double quote<br>
       * | \\ // backslash<br>
       * | octal-escape<br>
       * | unicode-escape<br>
       * octal-escape ::= \ octal-digit [ octal-digit ] | <br>
       * \ zero-to-three octal-digit octal-digit <br>
       * zero-to-three ::= 0 | 1 | 2 | 3 <br>
       * unicode-escape ::= \ u hex-digit hex-digit hex-digit hex-digit Note: No
       * whitespace between backslash and u
       */
      if (end - pos < 2) {
         throw new ParserException("Expected an escape sequence", text, pos);
      }
      if (text.charAt(pos) != '\\') {
         throw new ParserException("Expected a \\", text, pos);
      }
      final char escapedChar = text.charAt(pos + 1);
      switch (escapedChar) {
      case 'b':
      case 't':
      case 'n':
      case 'r':
      case '\'':
      case '\"':
      case '\\':
         return pos + 2;
      case 'u':
         // Unicode escape, need four hex digits
         for (int i = pos + 2; i < pos + 6; i++) {
            if (i < end && !isHexDigit(text.charAt(i))) {
               throw new ParserException("Invalid unicode escape", text, i);
            }
         }
         return pos + 6;
      default:
         // octal escape
         if (isOctalDigit(escapedChar)) {
            int maxNum = 2;
            if ('0' <= escapedChar && escapedChar <= '3') {
               maxNum++;
            }
            for (int i = pos + 2; i < pos + maxNum + 1; i++) {
               if (i < end && !isOctalDigit(text.charAt(i))) {
                  return i;
               }
            }
            return pos + maxNum + 1;
         }
         else {
            throw new ParserException("Illegal escale sequence", text, pos + 1);
         }
      }
   }

   public static int findNextWhitespace(final String text, final int start,
         final int end) throws ParserException {
      ParserUtils.validatePositions(text, start, end);
      int position = start;
      while (position < end && !Character.isWhitespace(text.charAt(position))) {
         position++;
      }
      if (position == end) {
         throw new ParserException("No whitespace found", text, end);
      }
      return position;
   }

   /**
    * Shortcut for {@link #skipLayout(String, int, int, boolean)} with
    * beginNewLine = false.
    *
    * @param text
    *           the text to skip in
    * @param start
    *           the start position
    * @param end
    *           the maximum end position
    * @return the exclusive end position of the layout
    * @throws ParserException
    *            if the positions are invalid
    */
   public static int skipLayout(final String text, final int start,
         final int end) throws ParserException {
      return skipLayout(text, start, end, false);
   }

   /**
    * Skips layout in the given text at the given start position. Layout is
    * whitespaces, the at sign after a new line and single line comments.
    *
    * @param text
    *           the text to skip in
    * @param start
    *           the start position
    * @param end
    *           the maximum end position
    * @param beginAtNewLine
    *           whether skipLayout is called in a new line, such a at sign is
    *           valid at the begin
    * @return the exclusive end position of the layout
    * @throws ParserException
    *            if the positions are invalid
    */
   public static int skipLayout(final String text, final int start,
         final int end, final boolean beginAtNewLine) throws ParserException {
      ParserUtils.validatePositions(text, start, end);
      int position = start;
      boolean inNewLine = beginAtNewLine;
      boolean nonWhiteSpaceFound = false;
      while (!nonWhiteSpaceFound && position < end) {

         final char c = text.charAt(position);

         if (c == '\n') {
            // Remember new lines because @ are layout only after newlines
            inNewLine = true;
            position++;
         }
         else if (Character.isWhitespace(c)) {
            // White space is always layout
            position++;
         }
         else if (c == '@') {
            // @ are only layout after a new line
            if (!inNewLine) {
               nonWhiteSpaceFound = true;
            }
            else {
               position++;
            }
         }
         else if (c == '/') {
            // Oh, could be a comment, need to check that
            if (position + 1 < end) {
               final char nextC = text.charAt(position + 1);
               if (nextC == '/') {
                  // Single line comment: skip until the next newline
                  final int singleCommentEnd = text.indexOf('\n', position);
                  if (singleCommentEnd == -1) {
                     position = end;
                  }
                  else {
                     position = Math.min(end, singleCommentEnd);
                  }
               }
               else {
                  // No comment
                  nonWhiteSpaceFound = true;
               }
            }
            else {
               // No comment
               nonWhiteSpaceFound = true;
            }
         }
         else {
            nonWhiteSpaceFound = true;
         }
      }
      // Accept an @ at the very last position of the comment
      if (position < end && text.charAt(position) == '@' && position + 1 == end) {
         position++;
      }
      return position;
   }
}
