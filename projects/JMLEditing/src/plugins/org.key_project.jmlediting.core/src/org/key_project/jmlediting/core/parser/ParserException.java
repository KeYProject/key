package org.key_project.jmlediting.core.parser;

/**
 * A ParserException signals that parsing was not successful for a given text at
 * a given position.
 *
 * @author Moritz Lichter
 *
 */
public class ParserException extends Exception {

   /**
    *
    */
   private static final long serialVersionUID = -2460850374879778841L;
   /**
    * The text to parse in.
    */
   private final String text;
   /**
    * The index of failure.
    */
   private final int index;

   /**
    * Creates a new {@link ParserException} with the given error message, the
    * given text including the error and the index of failure.
    *
    * @param message
    *           the error message
    * @param text
    *           the text unable to parse
    * @param index
    *           the error index
    * @param t
    *           the problem which caused the exception
    */
   public ParserException(final String message, final String text,
         final int index, final Throwable t) {
      super(message, t);
      this.text = text;
      this.index = index;
   }

   /**
    * Creates a new {@link ParserException} with the given error message, the
    * given text including the error and the index of failure.
    *
    * @param message
    *           the error message
    * @param text
    *           the text unable to parse
    * @param index
    *           the error index
    */
   public ParserException(final String message, final String text,
         final int index) {
      this(message, text, index, null);
   }

   @Override
   public String getMessage() {
      return super.getMessage() + " at " + this.index + "\n"
            + this.formatString();
   }

   /**
    * Formats the message to show a marker, where the problem occurred. It
    * removes lines breaks in the text to format and adds a new line with the
    * error marker.
    * 
    * @return a formatted message text
    */
   private String formatString() {
      String outputText = "";
      String outputMarker = "";
      int pos = 0;
      for (final char c : this.text.toCharArray()) {
         switch (c) {
         case '\n':
            outputText += "\\n";
            outputMarker += "  ";
            break;
         case '\t':
            outputText += "\\t";
            outputMarker += "  ";
            break;
         default:
            outputText += c;
            if (pos == this.index) {
               outputMarker += '^';
            }
            else {
               outputMarker += ' ';
            }
         }
         pos++;
      }
      return outputText + "\n" + outputMarker;
   }

}
