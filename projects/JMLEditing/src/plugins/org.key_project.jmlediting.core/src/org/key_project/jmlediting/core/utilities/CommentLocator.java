package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

import javax.swing.text.BadLocationException;

import org.key_project.jmlediting.core.utilities.CommentRange.CommentType;

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
      if (text == null) {
         throw new IllegalArgumentException("text must not be null!");
      }
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
   public boolean isInJMLComment(final int offset) {
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
   public List<CommentRange> findCommentRanges() {
      final List<CommentRange> comments = new ArrayList<CommentRange>();

      final char[] content = this.text.toCharArray();
      int position = 0;
      int begin = 0;
      ScannerState state = ScannerState.DEFAULT;

      mainloop: while (position < content.length) {
         final char c = content[position];
         switch (state) {
         // DefaultState
         case DEFAULT:
            switch (c) {
            // String Opener found
            case '"':
               state = ScannerState.IN_STRING;
               position += 1;
               break;
               // char opener found
            case '\'':
               state = ScannerState.IN_CHAR;
               position += 1;
               break;
               // comment opener found
            case '/':
               if (position < content.length - 1) {
                  final char c2 = content[position + 1];
                  switch (c2) {
                  // singleLine Comment found
                  case '/':
                     final int end = this.text.indexOf('\n', position);
                     // Comment end is inclusive
                     int commentEnd = end - 1;
                     if (end == -1) {
                        commentEnd = content.length - 1;
                     }
                     comments.add(new CommentRange(position, commentEnd,
                           position + 2, commentEnd, CommentType.SINGLE_LINE));
                     if (end == -1) {
                        break mainloop;
                     }
                     else {
                        position = end + 1;
                     }
                     break;
                     // Multiline Comment Opener found
                  case '*':
                     begin = position;
                     position += 2;
                     state = ScannerState.IN_COMMENT;
                     break;
                     // wrong combination of signs, ignore because there will be
                     // compile errors
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
               // no special sign found
            default:
               position += 1;
               break;
            }
            break;
         case IN_COMMENT:
            switch (c) {
            // possible begin of MultilineComment Closer found
            case '*':
               if (position < content.length - 1) {
                  final char c2 = content[position + 1];
                  switch (c2) {
                  // MultiLine Comment Closer found
                  case '/':
                     comments.add(new CommentRange(begin, position + 1,
                           begin + 2, position - 1, CommentType.MULTI_LINE));
                     state = ScannerState.DEFAULT;
                     position += 2;
                     break;
                     // star found, can be ignored because no / was found after
                  default:
                     position += 1;
                     break;
                  }
               }
               else {
                  break mainloop;
               }
               break;
               // no special sign found
            default:
               position += 1;
               break;
            }
            if (position == content.length) {
               comments.add(new CommentRange(begin, position - 1, begin + 2,
                     position - 1, CommentType.MULTI_LINE));
            }
            break;
         case IN_STRING:
            switch (c) {
            // String Closer found
            case '"':
               state = ScannerState.DEFAULT;
               position += 1;
               break;
               // Escape sign found
            case '\\':
               position += 2;
               break;
               // no special sign found
            default:
               position += 1;
               break;
            }
            break;
         case IN_CHAR:
            switch (c) {
            // Escape sign found
            case '\\':
               position += 2;
               break;
               // Char Closer found
            case '\'':
               state = ScannerState.DEFAULT;
               position += 1;
               break;
               // no special sign found
            default:
               position += 1;
               break;
            }
            break;
            // in unexpected state
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
      final List<CommentRange> comments = this.findCommentRanges();
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
      final List<CommentRange> jmlcomments = this.findCommentRanges();
      for (final CommentRange c : jmlcomments) {
         if (c.getBeginOffset() <= offset && offset <= c.getEndOffset()) {
            return c;
         }

      }
      return null;
   }
}
