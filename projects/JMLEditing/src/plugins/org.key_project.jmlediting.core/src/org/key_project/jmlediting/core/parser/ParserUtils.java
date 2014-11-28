package org.key_project.jmlediting.core.parser;

public class ParserUtils {

   public static void validatePositions(String text, int start, int end)
         throws ParserException {
      if (start < 0) {
         throw new ParserException("Given start index is out of bounds: "
               + start + " < 0", text, start);
      }
      if (start > text.length()) {
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
