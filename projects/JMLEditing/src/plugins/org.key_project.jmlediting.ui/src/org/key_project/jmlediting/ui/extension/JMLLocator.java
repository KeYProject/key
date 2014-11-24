package org.key_project.jmlediting.ui.extension;

import java.util.LinkedList;
import java.util.ListIterator;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

public class JMLLocator {

   private IDocument document;
   
   public JMLLocator(IDocument doc){
      this.document=doc;
   }
   
   /**
    * seeks the Documents text for JML Single Line comments
    * 
    * @return A Linked List of JML Comment sections which is empty if there are
    *         no singleLineComments
    */
   public LinkedList<Comment> findSingleLineJMLComment()
         throws BadLocationException {
      String text = document.get();
      int begin;
      int end;
      int lastIndex = 0;
      LinkedList<Comment> singleLineComments = new LinkedList<Comment>();

      while (true) {
         begin = text.indexOf("//@", lastIndex);
         if (begin == -1)
            return singleLineComments;
         end = document.getLineLength(document.getLineOfOffset(begin));
         singleLineComments.add(new Comment(begin, end));
         if (document.getNumberOfLines() == document.getLineOfOffset(begin))
            return singleLineComments;
      }
   }

   /**
    * seeks the Documents text for JML Multi Line comments
    * 
    * @return A Linked List of JML Comment sections
    */
   public LinkedList<Comment> findMultilineJMLComments() {
      String text = document.get();
      int lastIndex = 0;
      int begin;
      int end;
      LinkedList<Comment> comments = new LinkedList<Comment>();

      while (lastIndex > -1) {
         begin = text.indexOf("/*@", lastIndex);
         if (begin > -1) // Stop searching When End of File is reached
            lastIndex = begin;
         else
            return comments;
         end = text.indexOf("@*/", lastIndex);
         if (lastIndex > -1) // Stop searching When End of File is reached
            lastIndex = end;
         else
            return comments;
         end = end - begin;
         System.out.println("Comment found: Begin: " + begin + " length: "
               + end);
         comments.add(new Comment(begin, end));
      }
      System.out.println(text.indexOf("/*@"));
      return comments;
   }

   /**
    * isInJMLcomment checks whether an offset position is inside a JML Multiline
    * Comment Section
    * 
    * @param offset
    *           The offset to check whether it is in a JML Comment
    * @return true if offset is in a JML Comment, false if not
    * @throws BadLocationException
    */
   public boolean isInJMLcomment(int offset) throws BadLocationException {
      LinkedList<Comment> comments = findMultilineJMLComments();
      comments.addAll(findSingleLineJMLComment());
      int commentOffset;
      int commentLength;
      for (ListIterator<Comment> i = comments.listIterator(); i.hasNext(); i
            .next()) {
         commentOffset = i.next().offset;
         commentLength = i.next().length;
         if (commentOffset <= offset && commentLength + commentOffset >= offset)
            return true;
      }
      return false;
   }

}
