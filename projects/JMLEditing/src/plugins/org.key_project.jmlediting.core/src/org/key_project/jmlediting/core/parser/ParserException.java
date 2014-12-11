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
   private final int errorOffset;

   /**
    * Creates a new {@link ParserException} with the given error message, the
    * given text including the error and the index of failure.
    *
    * @param message
    *           the error message
    * @param text
    *           the text unable to parse
    * @param errorOffset
    *           the error offset in the text
    * @param t
    *           the problem which caused the exception
    */
   public ParserException(final String message, final String text,
         final int errorOffset, final Throwable t) {
      super(message, t);
      this.text = text;
      this.errorOffset = errorOffset;
   }

   /**
    * Creates a new {@link ParserException} with the given error message, the
    * given text including the error and the index of failure.
    *
    * @param message
    *           the error message
    * @param text
    *           the text unable to parse
    * @param errorOffset
    *           the error offset in the text
    */
   public ParserException(final String message, final String text,
         final int errorOffset) {
      this(message, text, errorOffset, null);
   }

   @Override
   public String getMessage() {
      return super.getMessage() + " at " + this.errorOffset + "\n"
            + this.formatString();
   }

   /**
    * Returns the offset in the text where the error occurred.
    * 
    * @return the error offset
    */
   public int getErrorOffset() {
      return this.errorOffset;
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
            if (pos == this.errorOffset) {
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
