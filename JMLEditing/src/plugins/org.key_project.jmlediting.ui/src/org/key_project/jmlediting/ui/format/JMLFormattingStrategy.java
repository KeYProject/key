package org.key_project.jmlediting.ui.format;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TypedPosition;
import org.eclipse.jface.text.formatter.FormattingContextProperties;
import org.eclipse.jface.text.formatter.IFormattingContext;
import org.eclipse.jface.text.formatter.IFormattingStrategy;
import org.eclipse.jface.text.formatter.IFormattingStrategyExtension;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.util.LogUtil;

/**
 * The {@link JMLFormattingStrategy} is a wrapper for another
 * {@link IFormattingStrategyExtension} which formats all non JML content. By
 * now, JML Code stays unchanged.
 *
 * @author Moritz Lichter
 *
 * @param <T>
 *           the type of the wrapped formatting strategy
 */
// The generic type T is necessary to enforce the type system to allow only
// wrapped instances which implements both interfaces
public class JMLFormattingStrategy<T extends IFormattingStrategy & IFormattingStrategyExtension>
      implements IFormattingStrategy, IFormattingStrategyExtension {

   /**
    * The wrapped strategy instance.
    */
   private final T wrappedStrategy;

   /**
    * Data class which contains the data for formatting a single document.
    *
    * @author Moritz Lichter
    *
    */
   private static class JMLFormatTask {
      /**
       * The document to format.
       */
      private IDocument doc;
      /**
       * The extracted JML comments.
       */
      private List<String> extractedComments;
      /**
       * The marker string which is used to indicate the position of JML
       * comments in the text given to the wrapped strategy.
       */
      private String commentMarker;
      /**
       * The original text of the document before formattin.
       */
      private String originalText;

   }

   /**
    * A list which contains all active tasks.
    */
   private final List<JMLFormatTask> tasks;

   /**
    * Creates a new JMLFormattingStrategy which wraps the given strategy.
    *
    * @param wrappedStrategy
    *           the strategy to wrap, not allowed to be null
    */
   public JMLFormattingStrategy(final T wrappedStrategy) {
      super();
      if (wrappedStrategy == null) {
         throw new IllegalArgumentException(
               "null is not allowed as wrapped strategy");
      }
      this.wrappedStrategy = wrappedStrategy;
      this.tasks = new ArrayList<JMLFormattingStrategy.JMLFormatTask>();
   }

   @Override
   public String format(final String content, final boolean start,
         final String indentation, final int[] positions) {
      // Usually this does nothing in implementations of
      // IFormattingStrategyExtension
      return this.wrappedStrategy
            .format(content, start, indentation, positions);
   }

   @Override
   public void formatterStarts(final IFormattingContext context) {

      // Goal: Modify the document to not contain JML comments but dummy
      // comments which allow to insert the JML comments later again
      final JMLFormatTask task = new JMLFormatTask();

      final IDocument doc = (IDocument) context
            .getProperty(FormattingContextProperties.CONTEXT_MEDIUM);
      task.doc = doc;
      task.originalText = doc.get();

      final TypedPosition position = (TypedPosition) context
            .getProperty(FormattingContextProperties.CONTEXT_PARTITION);

      final String content = doc.get();
      // This marker will be used in the comments for JML
      // the marker is guaranteed not to be in the content
      final String marker = calculateJMLCommentMarker(content);
      task.commentMarker = marker;

      // Here go all JML comments in
      final List<String> jmlComments = new ArrayList<String>();

      // Ranges of JML comments to remove, remove only them in the formatting
      // offset
      final List<CommentRange> jmlCommentRanges = new ArrayList<CommentRange>();
      // The dummy marker comments as replacements for the comments in the ist
      // above
      final List<String> jmlCommentMarker = new ArrayList<String>();

      // The dummy comments try to have the same length but may be longer if the
      // comment is shorter than the marker
      int offset = 0;
      // Filter the existing comment
      for (final CommentRange comment : new CommentLocator(content)
            .findJMLCommentRanges()) {
         // Only handle comments in formatter position
         if (position.overlapsWith(comment.getBeginOffset(),
               comment.getLength())) {

            // Remember to range to replace, the dummy content to insert and the
            // original text
            jmlCommentRanges.add(comment);
            final String dummyComment = dummyComment(comment, marker);
            jmlCommentMarker.add(dummyComment);
            jmlComments.add(content.substring(comment.getBeginOffset(),
                  comment.getEndOffset() + 1));

            // Adapt the offset
            assert dummyComment.length() >= comment.getLength();
            offset += dummyComment.length() - comment.getLength();

         }

      }
      task.extractedComments = jmlComments;
      // Set the offset to the position
      position.length += offset;

      // Create the content to be formatted
      final String javaContent = replaceWith(content, jmlCommentRanges,
            jmlCommentMarker);
      assert content.length() <= javaContent.length();
      doc.set(javaContent);
      context.setProperty(FormattingContextProperties.CONTEXT_MEDIUM, doc);

      this.tasks.add(task);
      // Now give the java formatter the modified document
      this.wrappedStrategy.formatterStarts(context);

   }

   @Override
   public void format() {
      this.wrappedStrategy.format();
      // Formatting of all documents is completed, insert the JML comment again

      for (final JMLFormatTask task : this.tasks) {
         try {
            final IDocument doc = task.doc;
            // Get remembered comments and marker
            final List<String> comments = task.extractedComments;
            final String marker = task.commentMarker;

            // Filter the comment ranges in the document for the marker comments
            final List<CommentRange> destinations = new ArrayList<CommentRange>();
            for (final CommentRange range : new CommentLocator(doc.get())
                  .findCommentRanges()) {
               // Because the marker can only occur in the marker comments, a
               // contains check is valid
               if (doc.get(range.getBeginOffset(), range.getLength()).contains(
                     marker)) {
                  destinations.add(range);
               }
            }
            if (destinations.size() != comments.size()) {
               // This should not happen: formatter did something strange and
               // marker comments get lost
               throw new BadLocationException(
                     "Wrong number of dummy comments detected.");
            }

            // Now replace the destinations with the remembered comments
            final String content = doc.get();
            final String jmlContent = replaceWith(content, destinations,
                  comments);
            doc.set(jmlContent);
         }
         catch (final BadLocationException ex) {
            // Mhm, unable to process because something unexpected has happened
            LogUtil.getLogger().logError("JML Formatter is unable to reintegrate JML comments", ex);
            // Reset the document because otherwise JML comments get lost
            task.doc.set(task.originalText);
         }
      }
      this.tasks.clear();

   }

   /**
    * Replaces in the given content string the given ranges with the given
    * replace strings. Both list must have the same length. The range at index i
    * is replaced with the string at index i.
    *
    * @param content
    *           the string to replace something in
    * @param rangesToReplace
    *           the ranges which should be removed and replaced
    * @param replaceContent
    *           the content to replace
    * @return the modified string
    */
   private static String replaceWith(final String content,
         final List<CommentRange> rangesToReplace,
         final List<String> replaceContent) {

      if (rangesToReplace.size() != replaceContent.size()) {
         throw new IllegalArgumentException(
               "Both lists have to have the same size");
      }

      String newContent = "";
      int lastPosition = 0;
      for (int i = 0; i < rangesToReplace.size(); i++) {
         final CommentRange comment = rangesToReplace.get(i);
         final String replace = replaceContent.get(i);

         // Add the content before the range to replace
         newContent += content
               .substring(lastPosition, comment.getBeginOffset());
         // And instead of the range the replace text
         newContent += replace;
         // End Offset inclusive -> add one
         lastPosition = comment.getEndOffset() + 1;

      }
      // Add the tailing rest
      newContent += content.subSequence(lastPosition, content.length());
      return newContent;
   }

   /**
    * Calculates a marker string which can be used to mark comments where a JML
    * comment was placed in the original document. The returned string is
    * guaranteed to to occur in the document and to consist only of upper case
    * letters. So the formatter will not produce a sequence in the rest of
    * document which is equal to the returned string.
    *
    * @param docContent
    *           the document content
    * @return a marker string
    */
   private static String calculateJMLCommentMarker(final String docContent) {
      String str = "";

      // Create a random string of upper case letters until it is not included
      // in the
      // document any more.

      // Range of the upper case characters in the ascii code
      final int upperCaseStart = 65;
      final int upperCaseEnd = 90;

      // The step size: as many characters will be added in each iteration to
      // reduce the number of contains calls
      final int stepSize = 5;

      // This loop is guaranteed to terminate because the length of docContent
      // increases and at some point it is larger then str
      // Usually the loop terminates after the first iteration
      while (docContent.contains(str)) {
         // Add random characters
         for (int i = 0; i < stepSize; i++) {
            final char nextChar = (char) Math.round(upperCaseStart
                  + (Math.random() * (upperCaseEnd - upperCaseStart)));
            assert Character.isUpperCase(nextChar);
            str += nextChar;
         }
      }
      return str;
   }

   /**
    * Creates a dummy comment with the given marker. The content tries to have
    * the same length as the original comment. Is is guaranteed not to be
    * shorter.
    *
    * @param comment
    *           the comment to create a dummy for
    * @param marker
    *           the marker string
    * @return a dummy comment containing the marker string which is as least as
    *         long as length
    */
   private static String dummyComment(final CommentRange comment,
         final String marker) {
      // The minimum length of comment start and end sign
      // Create a multi or single line comment depending on the give one
      final int minLength;
      String prefix;
      String suffix;
      switch (comment.getType()) {
      case MULTI_LINE:
         prefix = "/*";
         suffix = "*/";
         break;
      case SINGLE_LINE:
         prefix = "//";
         suffix = "";
         break;
      default:
         throw new AssertionError("Illegal state");
      }
      minLength = prefix.length() + suffix.length();

      // BUild the string
      String str = prefix + marker;
      // Insert whitespaces to fill up to the given length
      str += whiteSpaces(Math.max(0,
            comment.getLength() - minLength - marker.length()));
      str += suffix;
      return str;
   }

   /**
    * Creates a String containing length whitespaces.
    *
    * @param length
    *           the number of whitespaces
    * @return the string
    */
   private static String whiteSpaces(final int length) {
      final char[] c = new char[length];
      Arrays.fill(c, ' ');
      return new String(c);
   }

   @Override
   public void formatterStarts(final String initialIndentation) {
      this.wrappedStrategy.formatterStarts(initialIndentation);
   }

   @Override
   public void formatterStops() {
      this.wrappedStrategy.formatterStops();
   }

}
