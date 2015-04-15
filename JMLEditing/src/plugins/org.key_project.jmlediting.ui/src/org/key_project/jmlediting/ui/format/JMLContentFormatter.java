package org.key_project.jmlediting.ui.format;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.formatter.IContentFormatter;
import org.eclipse.jface.text.formatter.IContentFormatterExtension;
import org.eclipse.jface.text.formatter.IFormattingContext;
import org.eclipse.jface.text.formatter.IFormattingStrategy;
import org.eclipse.jface.text.formatter.IFormattingStrategyExtension;
import org.eclipse.jface.text.formatter.MultiPassContentFormatter;
import org.key_project.util.java.ObjectUtil;

/**
 * The {@link JMLContentFormatter} formats code containing JML. Another
 * formatter is wrapped which is used to format the not JML code. The
 * {@link JMLFormattingStrategy} is used to format the code.
 *
 * @author Moritz Lichter
 *
 */
public class JMLContentFormatter implements IContentFormatter,
      IContentFormatterExtension {

   /**
    * The wrapped formatter instance.
    */
   private final MultiPassContentFormatter wrappedFormatter;

   /**
    * Creates a new {@link JMLContentFormatter} which wraps the given formatter
    * which formats the non JML part.
    *
    * @param wrappedFormatter
    *           the formatter to wrap, not allowed to be null
    * @throws UnableToInitializeJMLFormatterException
    *            if the formatter is not able to initialize because
    *            wrappedFormatter is not legal
    */
   @SuppressWarnings({ "unchecked", "rawtypes" })
   public JMLContentFormatter(final MultiPassContentFormatter wrappedFormatter)
         throws UnableToInitializeJMLFormatterException {
      super();
      if (wrappedFormatter == null) {
         throw new IllegalArgumentException(
               "Wrapped Formatter is not allowed to be null");
      }
      this.wrappedFormatter = wrappedFormatter;
      // The java formatter should contains a JavaFormattingStrategy object,
      // which we want to wrap
      // Unfortunately, there is no way to get this object from the stratey

      try {
         final Object masterStrategy = ObjectUtil.get(wrappedFormatter,
               "fMaster");
         if (masterStrategy instanceof IFormattingStrategy
               && masterStrategy instanceof IFormattingStrategyExtension) {
            // Cannot express in java that masterStrategy has the correct type
            // here ...
            this.wrappedFormatter.setMasterStrategy(new JMLFormattingStrategy(
                  (IFormattingStrategy) masterStrategy));
         }
         else {
            throw new UnableToInitializeJMLFormatterException(
                  "The master strategy of the given formatter has wrong type",
                  null);
         }
      }
      catch (final Exception e) {
         throw new UnableToInitializeJMLFormatterException(
               "Failed to extract master strategy", e);
      }
   }

   // The rest is just delegated

   @Override
   public void format(final IDocument document, final IRegion region) {
      this.wrappedFormatter.format(document, region);
   }

   @Override
   public IFormattingStrategy getFormattingStrategy(final String contentType) {
      return this.wrappedFormatter.getFormattingStrategy(contentType);
   }

   @Override
   public void format(final IDocument document, final IFormattingContext context) {
      this.wrappedFormatter.format(document, context);
   }

}
