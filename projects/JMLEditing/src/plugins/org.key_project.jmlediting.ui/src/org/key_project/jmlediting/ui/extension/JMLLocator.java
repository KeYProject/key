package org.key_project.jmlediting.ui.extension;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;

/**
 * Class for finding JML Comments in a given String. This class does not take
 * care of changes to the String! If the String changes a new Instance of the
 * JMLLocator is needed
 *
 * @author David Giessing
 */
public class JMLLocator {

   private final String text;

   public JMLLocator(final String text) {
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
   public boolean isInJMLcomment(final int offset) {
      return this.getJMLComment(offset) != null;
   }

   /**
    *
    * @param offset
    *           The offset for which to get a Surrounding JMLComment
    * @return returns a JMLCommentRange if the given offset is in between a
    *         JMLComment, null if not
    */
   public JMLCommentRange getJMLComment(final int offset) {
      final List<JMLCommentRange> jmlcomments = this.findJMLComments();
      for (final JMLCommentRange c : jmlcomments) {
         if (c.getBeginOffset() <= offset && offset <= c.getEndOffset()) {
            return c;
         }
      }
      return null;
   }

   /**
    * States for the Statemachine.
    *
    *
    *
    */
   private static enum ScannerState {
      IN_STRING, IN_COMMENT, IN_CHAR, DEFAULT
   }

   /**
    * Uses an Automata to search All Kind of Valid Comments in the given String.
    *
    * @return An ArrayList with Type Comment that consists of all valid Comments
    *         in the Document
    */
   public List<JMLCommentRange> findJMLComments() {
      final List<JMLCommentRange> commentRanges = new ArrayList<JMLCommentRange>();
      final List<JMLCommentRange> jmlCommentRanges = new ArrayList<JMLCommentRange>();
      final char[] content = this.text.toCharArray();
      int position = 0;
      int begin = 0;
      ScannerState state = ScannerState.DEFAULT;

      mainloop: while (position < content.length) {
         final char c = content[position];
         switch (state) {
         case DEFAULT:
            switch (c) {
            case '"':
               state = ScannerState.IN_STRING;
               position += 1;
               break;
            case '\'':
               state = ScannerState.IN_CHAR;
               position += 1;
               break;
            case '/':
               if (position < content.length - 1) {
                  final char c2 = content[position + 1];
                  switch (c2) {
                  case '/':
                     final int end = this.text.indexOf(
                           System.getProperty("line.separator"), position);
                     // Comment end is inclusive
                     int commentEnd = end - 1;
                     if (end == -1) {
                        commentEnd = content.length - 1;
                     }
                     if (content.length - 1 >= position + 2
                           && content[position + 2] == '@') {
                        commentRanges.add(new JMLCommentRange(position,
                              commentEnd, position + 2, commentEnd));
                     }
                     if (end == -1) {
                        break mainloop;
                     }
                     else {
                        position = end + 1;
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
                     break;
                  }
               }
               else {
                  break mainloop;
               }
               break;
            default:
               position += 1;
               break;
            }
            break;
         case IN_COMMENT:
            switch (c) {
            case '*':
               if (position < content.length - 1) {
                  final char c2 = content[position + 1];
                  switch (c2) {
                  case '/':
                     if (content.length - 1 >= position + 2
                     && content[begin + 2] == '@') {
                        commentRanges.add(new JMLCommentRange(begin,
                              position + 1, begin + 2, position - 1));
                     }
                     state = ScannerState.DEFAULT;
                     position += 2;
                     break;
                  default:
                     position += 1;
                     break;
                  }
               }
               else {
                  break mainloop;
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
               position += 2;
               break;
            default:
               position += 1;
               break;
            }
            break;
         case IN_CHAR:
            switch (c) {
            case '\\':
               position += 2;
               break;
            case '\'':
               state = ScannerState.DEFAULT;
               position += 1;
               break;
            default:
               position += 1;
               break;
            }
            break;
         default:
            throw new AssertionError("Invalid Enum State");
         }
      }
      for (final JMLCommentRange c : commentRanges) {
         // filter for jml comments, a comment is a JML comment if the 3rd sign
         // is an @
         if ((this.text.length() - 1 >= c.getBeginOffset() + 2)
               && this.text.charAt(c.getBeginOffset() + 2) == '@') {
            jmlCommentRanges.add(c);
         }
      }

      return jmlCommentRanges;
   }
}
