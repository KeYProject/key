package org.key_project.jmlediting.core.parser;

public class ParserException extends Exception{
   
   private String text;
   private int index;


   public ParserException(String message, String text, int index, Throwable arg1) {
      super(message, arg1);
      this.text = text;
      this.index = index;
   }

   public ParserException(String message, String text, int index) {
      super(message);
      this.text= text;
      this.index = index;
   }
   
   @Override
   public String getMessage() {
      return super.getMessage() + " at "+ index + " " + text;
   }

}
