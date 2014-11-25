package org.key_project.jmlediting.core.parser;

public class ParserException extends Exception{
   
   /**
    * 
    */
   private static final long serialVersionUID = -2460850374879778841L;
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
      return super.getMessage() + " at "+ index + "\n" + formatString();
   }
   
   private String formatString() {
      String outputText = "";
      String outputMarker = "";
      int pos = 0;
      for (char c : text.toCharArray()) {
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
            if (pos == index) {
               outputMarker += '^';
            } else {
               outputMarker += ' ';
            }
         }
         pos ++;
      }
      return outputText + "\n" + outputMarker;
   }

}
