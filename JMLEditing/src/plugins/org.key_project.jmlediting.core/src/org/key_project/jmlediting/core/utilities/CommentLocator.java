package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TextUtilities;
import org.key_project.jmlediting.core.utilities.CommentRange.CommentType;
import org.key_project.util.jdt.JDTUtil;

/**
 * Class for finding JML Comments in a given String. This class does not take
 * care of changes to the String! If the String changes a new Instance of the
 * JMLLocator is needed
 *
 * @author Richard Bubel and Martin Hentschel
 */
public final class CommentLocator {
   /**
    * Forbid instances.
    */
   private CommentLocator() {
   }
   
   public static CommentRange getJMLComment(IDocument document, int offset) {
      ITypedRegion region = findCommentRegion(document, offset);
      if (region != null) {
         return getJMLComment(document.get(), region);
      }
      else {
         return null;
      }
   }

   public static CommentRange getComment(String text, ITypedRegion damage) {
      return createCommentRange(damage.getOffset(), 
                                damage.getLength(), 
                                IJavaPartitions.JAVA_SINGLE_LINE_COMMENT.equals(damage.getType()));
   }

   public static CommentRange getJMLComment(String text, ITypedRegion damage) {
      if (isJMLComment(text, damage.getOffset())) {
         return createCommentRange(damage.getOffset(), 
                                   damage.getLength(), 
                                   IJavaPartitions.JAVA_SINGLE_LINE_COMMENT.equals(damage.getType()));
      }
      else {
         return null;
      }
   }
   
   public static boolean isJMLComment(String text, int commentStartOffset) {
      return text.length() - 1 >= commentStartOffset + 2 && 
             text.charAt(commentStartOffset + 2) == '@';
   }
   
   public static CommentRange createCommentRange(int startPosition, int length, boolean isLineComment) {
      int endContentOffset = isLineComment ? 0 : 2; 
      return new CommentRange(startPosition, 
            startPosition + length - 1, 
            startPosition + 2, 
            startPosition + length - 1 - endContentOffset,
            isLineComment ? CommentType.SINGLE_LINE : CommentType.MULTI_LINE);
   }
   
   /**
    * Returns the {@link ITypedRegion} of the current comment in an incomplete Java source file.
    * @param document The {@link IDocument}.
    * @param offset The offset of interest.
    * @return The {@link ITypedRegion} of the current comment or {@code null} if the given offset is not part of a comment.
    */
   public static ITypedRegion findCommentRegion(IDocument document, int offset) {
      try {
         ITypedRegion region = TextUtilities.getPartition(document, IJavaPartitions.JAVA_PARTITIONING, offset, false);
         if (IJavaPartitions.JAVA_SINGLE_LINE_COMMENT.equals(region.getType())
             || IJavaPartitions.JAVA_MULTI_LINE_COMMENT.equals(region.getType())) {
            return region;
         }
         else {
            return null;
         }
      }
      catch (org.eclipse.jface.text.BadLocationException e) {
         return null;
      }
   }

   public static List<CommentRange> listCommentRanges(String source) {
      return listCommentRanges((CompilationUnit) JDTUtil.parse(source));
   }

   public static List<CommentRange> listCommentRanges(CompilationUnit compilationUnit) {
      final List<CommentRange> comments = new ArrayList<CommentRange>();
      for (Object obj : compilationUnit.getCommentList()) {
         if (obj instanceof Comment) {
            Comment c = (Comment) obj;
            comments.add(createCommentRange(c.getStartPosition(), c.getLength(), c.isLineComment()));
         }
      }
      return comments;
   }

   public static List<CommentRange> listJMLCommentRanges(String source) {
      return listJMLCommentRanges(source, (CompilationUnit) JDTUtil.parse(source));
   }

   public static List<CommentRange> listJMLCommentRanges(String source, CompilationUnit compilationUnit) {
      final List<CommentRange> comments = new ArrayList<CommentRange>();
      for (Object obj : compilationUnit.getCommentList()) {
         if (obj instanceof Comment) {
            Comment c = (Comment) obj;
            if (isJMLComment(source, c.getStartPosition())) {
               comments.add(createCommentRange(c.getStartPosition(), c.getLength(), c.isLineComment()));
            }
         }
      }
      return comments;
   }
}
