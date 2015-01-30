package org.key_project.jmlediting.ui.format;

import org.eclipse.jdt.internal.ui.text.java.JavaFormattingContext;
import org.eclipse.jdt.internal.ui.text.java.JavaFormattingStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.formatter.FormattingContextProperties;
import org.eclipse.jface.text.formatter.IContentFormatter;
import org.eclipse.jface.text.formatter.IContentFormatterExtension;
import org.eclipse.jface.text.formatter.IFormattingContext;
import org.eclipse.jface.text.formatter.IFormattingStrategy;
import org.eclipse.jface.text.formatter.IFormattingStrategyExtension;
import org.eclipse.jface.text.formatter.MultiPassContentFormatter;

public class JMLContentFormatter implements IContentFormatter,
      IContentFormatterExtension {

   private final MultiPassContentFormatter wrappedFormatter;

   private class DoNothingStrategy implements IFormattingStrategy,
         IFormattingStrategyExtension {

      @Override
      public void formatterStarts(final String initialIndentation) {
         // TODO Auto-generated method stub

      }

      @Override
      public String format(final String content, final boolean isLineStart,
            final String indentation, final int[] positions) {
         return content;
      }

      @Override
      public void formatterStops() {
         // TODO Auto-generated method stub

      }

      @Override
      public void format() {
         // throw new RuntimeException();
      }

      @Override
      public void formatterStarts(final IFormattingContext context) {
         // TODO Auto-generated method stub

      }

   }

   public JMLContentFormatter(final IContentFormatter wrappedFormatter) {
      super();
      if (wrappedFormatter == null) {
         throw new IllegalArgumentException(
               "Wrapped Formatter is not allowed to be null");
      }
      System.out.println("Got: " + wrappedFormatter);
      this.wrappedFormatter = (MultiPassContentFormatter) wrappedFormatter;
      final JavaFormattingStrategy javaFormatter = new JavaFormattingStrategy();
      this.wrappedFormatter.setMasterStrategy(new JMLFormattingStrategy(
            javaFormatter));
   }

   @Override
   public void format(final IDocument document, final IRegion region) {
      System.out.println("format with: " + this.wrappedFormatter);
      this.wrappedFormatter.format(document, region);
   }

   @Override
   public IFormattingStrategy getFormattingStrategy(final String contentType) {
      System.out.println("Strategy for: " + contentType);
      final IFormattingStrategy strategy = this.wrappedFormatter
            .getFormattingStrategy(contentType);

      System.out.println("Got: " + strategy);
      return strategy;
   }

   @Override
   public void format(final IDocument document, final IFormattingContext context) {
      System.out.println("Format:" + context);
      final JavaFormattingContext jcontext = (JavaFormattingContext) context;
      System.out.println("Format in: "
            + jcontext
                  .getProperty(FormattingContextProperties.CONTEXT_PARTITION));
      ((IContentFormatterExtension) this.wrappedFormatter).format(document,
            context);
   }

}
