package org.key_project.jmlediting.ui.extension;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.presentation.IPresentationDamager;
import org.eclipse.jface.text.presentation.IPresentationRepairer;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;

public class JMLPresentationDamagerRepairer implements IPresentationDamager,
IPresentationRepairer {
   private final DefaultDamagerRepairer wrappedInstance;

   IDocument doc;

   public JMLPresentationDamagerRepairer(
         final DefaultDamagerRepairer wrappedInstance) {
      super();
      this.wrappedInstance = wrappedInstance;
   }

   @Override
   public void createPresentation(final TextPresentation presentation,
         final ITypedRegion damage) {
      boolean jml = false;
      final JMLLocator locator = new JMLLocator(this.doc.get());

      jml = locator.isInJMLcomment(damage.getOffset());

      if (jml) {
         final TextAttribute ta = new TextAttribute(new Color(
               Display.getDefault(), 255, 0, 0));
         this.addRange(presentation, damage.getOffset(), damage.getLength(), ta);
      }
      else {
         // Normal Java Comment
         this.wrappedInstance.createPresentation(presentation, damage);
      }
   }

   @Override
   public void setDocument(final IDocument document) {
      this.doc = document;
      this.wrappedInstance.setDocument(document);
   }

   @Override
   public IRegion getDamageRegion(final ITypedRegion partition,
         final DocumentEvent event, final boolean documentPartitioningChanged) {
      return this.wrappedInstance.getDamageRegion(partition, event,
            documentPartitioningChanged);
   }

   /**
    * Copied from {@link DefaultDamagerRepairer}.
    */
   protected void addRange(final TextPresentation presentation,
         final int offset, final int length, final TextAttribute attr) {
      if (attr != null) {
         final int style = attr.getStyle();
         final int fontStyle = style & (SWT.ITALIC | SWT.BOLD | SWT.NORMAL);
         final StyleRange styleRange = new StyleRange(offset, length,
               attr.getForeground(), attr.getBackground(), fontStyle);
         styleRange.strikeout = (style & TextAttribute.STRIKETHROUGH) != 0;
         styleRange.underline = (style & TextAttribute.UNDERLINE) != 0;
         styleRange.font = attr.getFont();
         presentation.addStyleRange(styleRange);
      }
   }
}
