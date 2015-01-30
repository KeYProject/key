package org.key_project.jmlediting.ui.format;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.ui.text.java.JavaFormattingStrategy;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TypedPosition;
import org.eclipse.jface.text.formatter.FormattingContextProperties;
import org.eclipse.jface.text.formatter.IFormattingContext;
import org.eclipse.jface.text.formatter.IFormattingStrategy;
import org.eclipse.jface.text.formatter.IFormattingStrategyExtension;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLFormattingStrategy implements IFormattingStrategy,
      IFormattingStrategyExtension {

   private final JavaFormattingStrategy javaFormattingStrategy;

   private final Map<IDocument, List<String>> rememberedJMLComments = new HashMap<IDocument, List<String>>();
   private final Map<IDocument, String> commentMarker = new HashMap<IDocument, String>();

   public JMLFormattingStrategy(
         final JavaFormattingStrategy javaFormattingStrategy) {
      super();
      this.javaFormattingStrategy = javaFormattingStrategy;
   }

   @Override
   public String format(final String content, final boolean start,
         final String indentation, final int[] positions) {
      return this.javaFormattingStrategy.format(content, start, indentation,
            positions);
   }

   @Override
   public void format() {
      this.javaFormattingStrategy.format();
      try {
         for (final IDocument doc : this.rememberedJMLComments.keySet()) {
            final List<String> comments = this.rememberedJMLComments.get(doc);
            final List<CommentRange> destinations = new ArrayList<CommentRange>();
            final String marker = this.commentMarker.get(doc);
            final CommentLocator locator = new CommentLocator(doc.get());

            for (final CommentRange range : locator.findCommentRanges()) {
               if (doc.get(range.getBeginOffset(), range.getLength()).contains(
                     marker)) {
                  destinations.add(range);
               }
            }

            final String content = doc.get();
            final String jmlContent = replaceWith(content, destinations,
                  comments);

            doc.set(jmlContent);
         }

      }
      catch (final BadLocationException ex) {
         ex.printStackTrace();
      }
   }

   @Override
   public void formatterStarts(final IFormattingContext context) {

      // CONTEXT_MEDIUM
      final IDocument doc = (IDocument) context
            .getProperty(FormattingContextProperties.CONTEXT_MEDIUM);

      final TypedPosition position = (TypedPosition) context
            .getProperty(FormattingContextProperties.CONTEXT_PARTITION);

      final List<String> jmlComments = new ArrayList<String>();

      final String content = doc.get();
      final String marker = calculateJMLCommentMarker(content);
      this.commentMarker.put(doc, marker);
      final CommentLocator locator = new CommentLocator(content);

      final List<CommentRange> jmlCommentRanges = new ArrayList<CommentRange>();
      final List<String> jmlCommentMarker = new ArrayList<String>();
      int offset = 0;
      for (final CommentRange comment : locator.findJMLCommentRanges()) {
         if (position.overlapsWith(comment.getBeginOffset(),
               comment.getLength())) {
            jmlCommentRanges.add(comment);
            final String dummyComment = dummyComment(comment.getLength(),
                  marker);
            offset += dummyComment.length() - comment.getLength();
            jmlCommentMarker.add(dummyComment);
            jmlComments.add(content.substring(comment.getBeginOffset(),
                  comment.getEndOffset() + 1));
         }

      }
      position.length += offset;

      final String javaContent = replaceWith(content, jmlCommentRanges,
            jmlCommentMarker);

      assert content.length() == javaContent.length();

      doc.set(javaContent);
      context.setProperty(FormattingContextProperties.CONTEXT_MEDIUM, doc);
      this.rememberedJMLComments.put(doc, jmlComments);
      this.javaFormattingStrategy.formatterStarts(context);

   }

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

         newContent += content
               .substring(lastPosition, comment.getBeginOffset());
         newContent += replace;
         lastPosition = comment.getEndOffset() + 1;

      }
      newContent += content.subSequence(lastPosition, content.length());
      return newContent;
   }

   private static String calculateJMLCommentMarker(final String docContent) {
      String str = "";

      final int upperCaseStart = 65;
      final int upperCaseEnd = 90;
      final int stepSize = 5;

      while (docContent.contains(str)) {
         for (int i = 0; i < stepSize; i++) {
            final char nextChar = (char) Math.round(upperCaseStart
                  + (Math.random() * (upperCaseEnd - upperCaseStart)));
            assert Character.isUpperCase(nextChar);
            str += nextChar;
         }
      }
      return str;
   }

   private static String dummyComment(final int length, final String marker) {
      String str = "/*" + marker;
      str += whiteSpaces(Math.max(0, length - 4 - marker.length()));
      str += "*/";
      return str;
   }

   private static String whiteSpaces(final int length) {
      final char[] c = new char[length];
      Arrays.fill(c, ' ');
      return new String(c);
   }

   @Override
   public void formatterStarts(final String initialIndentation) {
      this.javaFormattingStrategy.formatterStarts(initialIndentation);
   }

   @Override
   public void formatterStops() {
      this.javaFormattingStrategy.formatterStops();
   }

}
