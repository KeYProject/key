package org.key_project.jmlediting.core.parser;

public class ParserError {

   private final String errorText;
   private final int errorOffset;

   public ParserError(final String errorText, final int errorOffset) {
      super();
      this.errorText = errorText;
      this.errorOffset = errorOffset;
   }

   public int getErrorOffset() {
      return this.errorOffset;
   }

   public String getErrorText() {
      return this.errorText;
   }

}
