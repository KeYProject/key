package org.key_project.jmlediting.ui.extension;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

public class JMLLocator {

   private String text;

   public JMLLocator(String text) {
      this.text = text;
   }

   /**
    * isInJMLcomment checks whether an offset position is inside a JMLComment
    * 
    * @param offset
    *           The offset to check whether it is in a JML Comment
    * @return true if offset is in a JML Comment, false if not
    * @throws BadLocationException
    */
   public boolean isInJMLcomment(int offset) throws BadLocationException {
      List<Comment> jmlcomments = findJMLComments();
      for (Comment c : jmlcomments)
         if (c.offset <= offset && offset <= c.end)
            return true;
      return false;
   }

   private static enum ScannerState {
      IN_STRING, IN_COMMENT, IN_CHAR, DEFAULT
   }

   /**
    * Uses an Automata to search All Kind of Valid JMLComments in document
    * 
    * @return An ArrayList with Type Comment that consists of all valid
    *         JMLComments in the Document
    */
   public List<Comment> findJMLComments() {
      List<Comment> comments = new ArrayList<Comment>();
      List<Comment> jmlcomments = new ArrayList<Comment>();

      char[] content = text.toCharArray();
      int position = 0;
      int begin = 0;
      ScannerState state = ScannerState.DEFAULT;

      mainloop: while (position < content.length) {
         char c = content[position];
         switch (state) {
         case DEFAULT:
            switch (c) {
            case '"':
               state = ScannerState.IN_STRING;
               position += 1;
               break;
            case'\'':
               state = ScannerState.IN_CHAR;
               position +=1;
               break;
            case '/':
               if (position < content.length - 1) {
                  char c2 = content[position + 1];
                  switch (c2) {
                  case '/':
                     int end = text.indexOf(System.getProperty("line.separator"), position);
                     int commentEnd = end;
                     if (end == -1) {
                        commentEnd = content.length - 1;
                     }
                     comments.add(new Comment(position, commentEnd));
                     if (end == -1) {
                        break mainloop;
                     }
                     else {
                        position = end + 1;
                        state = ScannerState.DEFAULT;
                     }
                     break;
                  case '*':
                     begin = position;
                     position += 2;
                     state = ScannerState.IN_COMMENT;
                     break;
                  default:
                     position += 1;
                     state = ScannerState.DEFAULT;
                  }
               }
               default: position+=1;
            }
            break;
         case IN_COMMENT:
            switch (c) {
            case '*':
               if (position < content.length - 1) {
                  char c2 = content[position + 1];
                  switch (c2) {
                  case '/':
                     comments.add(new Comment(begin, position + 1));
                     state = ScannerState.DEFAULT;
                     position += 2;
                     break;
                  default:
                     position += 1;
                     break;
                  }
               }
               break;
            default:
               position += 1;
               break;
            }
            break;
         case IN_STRING:
            switch (c) {
            case '"':
               state = ScannerState.DEFAULT;
               position += 1;
               break;
            case '\\':
               position+=2;
               break;
            default:
               position += 1;
               break;
            }
            
            break;
         case IN_CHAR:
            switch(c){
            case '\\':
               position+=2;
               break;
            case '\'':
               state=ScannerState.DEFAULT;
               position+=1;
            }
            break;
         default:
            throw new AssertionError("Invalid Enum State");
         }
      }

      for (Comment c : comments)
         // filter for jml comments, a comment is a JML comment if the 3rd sign
         // is an @
         if ((text.length()-1<c.offset+2)&&text.charAt(c.offset + 2) == '@')
            jmlcomments.add(c);

      return jmlcomments;
   }
}
