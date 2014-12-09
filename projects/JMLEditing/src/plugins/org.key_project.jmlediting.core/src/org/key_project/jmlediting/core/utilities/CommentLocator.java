package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

/**
 * Class for finding JML Comments in a given String. This class does not take
 * care of changes to the String! If the String changes a new Instance of the
 * JMLLocator is needed
 *
 * @author David Giessing
 */
public class CommentLocator {
   /**
    * The text the Locator operates on.
    */
   private final String text;

   /**
    * Constructs a CommentLocator that operates on the given String.
    *
    * @param text
    *           the String to operate on
    */
   public CommentLocator(final String text) {
      this.text = text;
   }

   /**
    * isInJMLcomment checks whether an offset position is inside a JMLComment.
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
    * Finds a JMLComment containing the given offset.
    *
    * @param offset
    *           the Offset of the offset to search around
    * @return the CommentRange that contains the given offset or null if no JML
    *         comment surrounds the given offset
    */
   public CommentRange getJMLComment(final int offset) {
      final List<CommentRange> jmlcomments = this.findJMLCommentRanges();
      for (final CommentRange c : jmlcomments) {
         if (c.getBeginOffset() <= offset && offset <= c.getEndOffset()) {
            return c;
         }
      }
      return null;
   }

   /**
    * Uses an Automata to search All Kind of Valid Comments in the given String.
    *
    * @return An ArrayList with Type Comment that consists of all valid Comments
    *         in the Document
    */
   public List<CommentRange> findComments() {
      final List<CommentRange> comments = new ArrayList<CommentRange>();

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
                     final int end = this.text.indexOf('\n', position);
                     // Comment end is inclusive
                     int commentEnd = end - 1;
                     if (end == -1) {
                        commentEnd = content.length - 1;
                     }
                     comments.add(new CommentRange(position, commentEnd,
                           position + 2, commentEnd));
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
                     comments.add(new CommentRange(begin, position + 1,
                           begin + 2, position - 1));
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
      return comments;
   }

   /**
    * The automatas states.
    */
   private static enum ScannerState {
      IN_STRING, IN_COMMENT, IN_CHAR, DEFAULT
   }

   /**
    * Filters a List of Comments for JMLComments.
    *
    * @return An ArrayList with Type Comment that consists of all valid
    *         JMLComments in the Document
    */
   public List<CommentRange> findJMLCommentRanges() {
      final List<CommentRange> comments = this.findComments();
      final List<CommentRange> jmlcomments = new ArrayList<CommentRange>();

      for (final CommentRange c : comments) {
         // filter for jml comments, a comment is a JML comment if the 3rd sign
         // is an @
         if ((this.text.length() - 1 >= c.getBeginOffset() + 2)
               && this.text.charAt(c.getBeginOffset() + 2) == '@') {
            jmlcomments.add(c);
         }
      }

      return jmlcomments;
   }

   /**
    * Seeks for a valid Comment that surrounds the given Offset and returns it.
    *
    * @param offset
    *           The Offset to be inside the returned Comment
    * @return A Comment Object that is a Comment that surrounds the given
    *         offset, null if no comment is found around this offset
    */
   public CommentRange getCommentOfOffset(final int offset) {
      final List<CommentRange> jmlcomments = this.findComments();
      for (final CommentRange c : jmlcomments) {
         if (c.getBeginOffset() <= offset && offset <= c.getEndOffset()) {
            return c;
         }

      }
      return null;
   }
}
