package org.key_project.jmlediting.core.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;

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
   private final ParserError causedError;
   private final List<ParserError> allErrors;
   private final String parseContent;
   private final IASTNode errorNode;

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
      this(new ParserError(message, errorOffset), null, text, null, t);
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

   public ParserException(final ParserError error, final String text,
         final IASTNode errorNode) {
      this(error, null, text, errorNode, null);
   }

   public ParserException(final String message, final int errorOffset,
         final String text, final IASTNode errorNode) {
      this(new ParserError(message, errorOffset), null, text, errorNode, null);
   }

   private static final String getErrorMessage(final ParserError error,
         final List<ParserError> allErrors) {
      if (error == null && (allErrors == null || allErrors.isEmpty())) {
         throw new IllegalArgumentException(
               "Need to provide at least one error");
      }
      if (error != null) {
         return error.getErrorText();
      }
      else {
         return allErrors.get(0).getErrorText();
      }
   }

   public ParserException(final ParserError error,
         final List<ParserError> allErrors, final String text,
         final IASTNode errorNode, final Throwable cause) {
      super(getErrorMessage(error, allErrors), cause);
      this.causedError = error;
      this.errorNode = errorNode;
      this.parseContent = text;
      if (allErrors == null || allErrors.isEmpty()) {
         this.allErrors = Collections.singletonList(error);
      }
      else {
         if (error != null) {
            this.allErrors = new ArrayList<ParserError>(allErrors);
            this.allErrors.add(error);
         }
         else {
            this.allErrors = allErrors;
         }
      }
   }

   public ParserException(final ParserException old, final IASTNode newErrorNode) {
      this(null, old.allErrors, old.parseContent, newErrorNode, old);
   }

   @Override
   public String getMessage() {
      return super.getMessage() + " at " + this.causedError.getErrorOffset()
            + "\n" + this.formatString();
   }

   /**
    * Returns the offset in the text where the error occurred.
    *
    * @return the error offset
    */
   public int getErrorOffset() {
      return this.causedError.getErrorOffset();
   }

   public IASTNode getErrorNode() {
      return this.errorNode;
   }

   public List<ParserError> getAllErrors() {
      return this.allErrors;
   }

   public ParserError getCausedError() {
      return this.causedError;
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
      for (final char c : this.parseContent.toCharArray()) {
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
            if (pos == this.getErrorOffset()) {
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
