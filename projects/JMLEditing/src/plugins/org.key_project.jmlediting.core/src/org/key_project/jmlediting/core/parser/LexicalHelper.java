package org.key_project.jmlediting.core.parser;

import static org.key_project.jmlediting.core.parser.ParserUtils.*;

public class LexicalHelper {
   
   public static int scanForClosingSemicolon(String text, int start, int end)
         throws ParserException {
      boolean isStringOrChar = false;
      char quoteChar = ' ';
      int position = start;
      while (position < end) {
         char c = text.charAt(position);
         boolean isQuoteChar = c == '\'' || c == '\"';
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

   public static int getIdentifier(String text, int start, int end)
         throws ParserException {
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

   public static int skipWhiteSpacesOrAt(String text, int start, int end)
         throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      while (position < end
            && ((text.charAt(position) == '@') || isWhitespace(text
                  .charAt(position)))) {
         position++;
      }
      return position;
   }

   public static int skipWhiteSpaces(String text, int start, int end)
         throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      while (position < end && isWhitespace(text.charAt(position))) {
         position++;
      }
      return position;
   }

   public static boolean isWhitespace(char c) {
      return isWhitespaceWithoutNewLine(c) || c == '\n' || c == '\r';
   }

   public static boolean isWhitespaceWithoutNewLine(int c) {
      return c == ' ' || c == '\t';
   }

}
