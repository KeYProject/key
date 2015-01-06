package org.key_project.jmlediting.core.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;

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
    * The error, which caused this exception, the error might be null of the
    * exception is caused by another {@link ParserException}. Then the list of
    * all errors is not empty.
    */
   private final ParserError causedError;
   /**
    * The list of all other errors collected from children. It may be null or
    * empty only if the caused error is not empty.
    */
   private final List<ParserError> allErrors;
   /**
    * The String which has been tries to parse.
    */
   private final String parseInput;
   /**
    * An {@link IASTNode} which has been created for the wrong parse input. In
    * may contain error nodes holding the text which could not be parsed.It is
    * allowed to be null.
    */
   private final IASTNode errorNode;

   private static final String getErrorMessage(final ParserError error,
         final List<ParserError> allErrors) {
      if (error == null && (allErrors == null || allErrors.isEmpty())) {
         throw new IllegalArgumentException(
               "Need to provide at least one error");
      }
      if (error != null) {
         return error.getErrorMessage();
      }
      else {
         return allErrors.get(0).getErrorMessage();
      }
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

   /**
    * Creates a new {@link ParserException}.
    *
    * @param message
    *           the error message
    * @param errorOffset
    *           the offset where the error occurred
    * @param text
    *           the text tried to parse
    * @param errorNode
    *           the error node created for the content
    */
   public ParserException(final String message, final int errorOffset,
         final String text, final IASTNode errorNode) {
      this(new ParserError(message, errorOffset), null, text, errorNode, null);
   }

   /**
    * Creates a new {@link ParserException}. If error is null, allErrors is not
    * allowed to be null or empty. Otherwise an {@link IllegalArgumentException}
    * is thrown.
    *
    * @param error
    *           the error which causes this exception, may be null if the
    *           exception is caused by another exception
    * @param allErrors
    *           the list of all collected errors
    * @param text
    *           the text tried to parse
    * @param errorNode
    *           the error node for the text, may be null
    * @param cause
    *           the causing exception, may be null
    * @throws IllegalArgumentException
    *            if error is null and allErrors empty or null
    */
   public ParserException(final ParserError error,
         final List<ParserError> allErrors, final String text,
         final IASTNode errorNode, final Throwable cause) {
      // getErrorMessage picks a message from error or of the first error in
      // allErrors, if error is null
      // it throws the IllegalArgument exception if no error is available
      super(getErrorMessage(error, allErrors), cause);
      this.causedError = error;
      this.errorNode = errorNode;
      this.parseInput = text;
      if (allErrors == null || allErrors.isEmpty()) {
         this.allErrors = Collections.singletonList(error);
      }
      else {
         if (error != null) {
            // Dont modify tge input list
            this.allErrors = new ArrayList<ParserError>(allErrors);
            this.allErrors.add(error);
         }
         else {
            // We do not modify the error list, so no need to copy it
            this.allErrors = allErrors;
         }
      }
   }

   /**
    * Creates a new {@link ParserException} which is caused by the given
    * exception.
    *
    * @param old
    *           the exception which caused this exception
    * @param newErrorNode
    *           the new error node
    */
   public ParserException(final ParserException old, final IASTNode newErrorNode) {
      this(null, old.allErrors, old.parseInput, newErrorNode, old);
   }

   @Override
   public String getMessage() {
      ParserError error;
      if (this.causedError != null) {
         error = this.causedError;
      }
      else if (this.getCause() != null) {
         return this.getCause().getMessage();
      }
      else {
         error = this.allErrors.get(this.allErrors.size() - 1);
      }

      return super.getMessage() + " at " + error.getErrorOffset() + "\n"
            + this.formatString(error.getErrorOffset());
   }

   /**
    * Returns the offset in the text where the error occurred.
    *
    * @return the error offset
    */
   public int getErrorOffset() {
      ParserError error;
      if (this.causedError != null) {
         error = this.causedError;
      }
      else {
         error = this.allErrors.get(this.allErrors.size() - 1);
      }
      return error.getErrorOffset();
   }

   /**
    * Returns the error node. This is an AST node which may contain Nodes of
    * type {@link NodeTypes#ERROR_NODE}. They indicate positions where the
    * parser failed. The node may be null if no such node could be produced.
    *
    * @return the error node
    */
   public IASTNode getErrorNode() {
      return this.errorNode;
   }

   /**
    * Returns all errors which has been encountered during parsing.
    *
    * @return an unmodifiable list of all errors
    */
   public List<ParserError> getAllErrors() {
      return Collections.unmodifiableList(this.allErrors);
   }

   /**
    * Returns the {@link ParserError} which caused this exception, it may be
    * null.
    *
    * @return the causing error
    */
   public ParserError getCausedError() {
      return this.causedError;
   }

   /**
    * Formats the message to show a marker, where the problem occurred. It
    * removes lines breaks in the text to format and adds a new line with the
    * error marker.
    *
    * @param errorPos
    *           the position to mark as the error
    *
    * @return a formatted message text
    */
   private String formatString(final int errorPos) {
      String outputText = "";
      String outputMarker = "";
      int pos = 0;
      for (final char c : this.parseInput.toCharArray()) {
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
            if (pos == errorPos) {
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
