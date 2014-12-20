package org.key_project.jmlediting.core.parser;

/**
 * A {@link ParserError} is an error found while parsing the input text.
 *
 * @author Moritz Lichter
 *
 */
public class ParserError {

   /**
    * A message text describing the error.
    */
   private final String errorMessage;
   /**
    * The offset in this text where a parsing error occurred.
    */
   private final int errorOffset;

   /**
    * Creates a new {@link ParserError}.
    *
    * @param errorText
    *           the error message
    * @param errorOffset
    *           the offset of the error
    */
   public ParserError(final String errorText, final int errorOffset) {
      super();
      this.errorMessage = errorText;
      this.errorOffset = errorOffset;
   }

   /**
    * Returns the error offset in the input text.
    *
    * @return the error offset
    */
   public int getErrorOffset() {
      return this.errorOffset;
   }

   /**
    * Returns the error message.
    *
    * @return the error message
    */
   public String getErrorMessage() {
      return this.errorMessage;
   }

}
