package org.key_project.jmlediting.ui.extension;

import java.util.ArrayList;

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
      ArrayList<Comment> jmlcomments = findJMLComments();
      for(Comment c:jmlcomments)
         if(c.offset<=offset&&offset<=c.end)
            return true;
      return false;
   }

   /**
    * Uses an Automata to search All Kind of Valid JMLComments in document
    * 
    * @return An ArrayList with Type Comment that consists of all valid
    *         JMLComments in the Document
    */
   public ArrayList<Comment> findJMLComments() {
      boolean state = false; // false is the default state, true is the state
                             // where a "/" was recognized
      int begin = 0;
      ArrayList<Comment> comments = new ArrayList<Comment>();
      ArrayList<Comment> jmlcomments = new ArrayList<Comment>();

      for (int i = 0; i < text.length() - 1; i++) {
         if (!state) {                             //if no Prefix sign was detected
            if (text.charAt(i) == '"') {           //if actual sign is a StringOpener find the end of the String
               i = text.indexOf("\"", i + 1) + 1;  // and change index from where to process
               if (i == -1)                        // if EndOfFile is reached stop the loop
                  break;
            }
            else if (text.charAt(i) == '/')        //if / was detected change State into / Prefix State
               state = true;
            else
               continue;
         }
         else if(text.charAt(i)=='/'){          //if Second / is detected SingleLineComment was found
            begin=i-1;
            i=text.indexOf(System.getProperty("line.separator"),begin+1);  //set index to end of line
            comments.add(new Comment(begin,i+1));                        //add found comment to list of comments
            state=false;                                                 //return to no Prefix State
         }
         else if(text.charAt(i)=='*'){             //if * is detected in / Prefix state MultilineComment was found
            begin=i-1;
         i=text.indexOf("*/",begin)+1;             //set index to end of MultilineComment
         comments.add(new Comment(begin,i+1));     //add comment
         state=false;                              //return to no prefix state
         }
         else state=false;                         //failure return to no prefix state
      }
      
      for(Comment c:comments)                  //filter for jml comments, a comment is a JML comment if the 3rd sign is an @
         if(text.charAt(c.offset+2)=='@')
            jmlcomments.add(c);
      
      return jmlcomments;
   }
}
