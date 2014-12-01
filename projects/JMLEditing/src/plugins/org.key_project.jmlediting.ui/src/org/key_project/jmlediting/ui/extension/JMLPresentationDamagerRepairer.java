package org.key_project.jmlediting.ui.extension;

import javax.swing.text.Document;

import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPositionCategoryException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
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

   public JMLPresentationDamagerRepairer(DefaultDamagerRepairer wrappedInstance) {
      super();
      this.wrappedInstance = wrappedInstance;
   }

   @Override
   public void createPresentation(TextPresentation presentation,
         ITypedRegion damage) {
      boolean jml = false;
      JMLLocator locator = new JMLLocator(doc.get());
      try {
         jml = locator.isInJMLcomment(damage.getOffset());
      }
      catch (BadLocationException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      if (jml) {
         TextAttribute ta = new TextAttribute(new Color(Display.getDefault(),
               255, 0, 0));
         addRange(presentation, damage.getOffset(), damage.getLength(), ta);
      }
      else {
         // Normal Java Comment
         wrappedInstance.createPresentation(presentation, damage);
      }
   }

   @Override
   public void setDocument(IDocument document) {
      doc = document;
      wrappedInstance.setDocument(document);
   }

   @Override
   public IRegion getDamageRegion(ITypedRegion partition, DocumentEvent event,
         boolean documentPartitioningChanged) {
      return wrappedInstance.getDamageRegion(partition, event,
            documentPartitioningChanged);
   }

   /**
    * Copied from {@link DefaultDamagerRepairer}.
    */
   protected void addRange(TextPresentation presentation, int offset,
         int length, TextAttribute attr) {
      if (attr != null) {
         int style = attr.getStyle();
         int fontStyle = style & (SWT.ITALIC | SWT.BOLD | SWT.NORMAL);
         StyleRange styleRange = new StyleRange(offset, length,
               attr.getForeground(), attr.getBackground(), fontStyle);
         styleRange.strikeout = (style & TextAttribute.STRIKETHROUGH) != 0;
         styleRange.underline = (style & TextAttribute.UNDERLINE) != 0;
         styleRange.font = attr.getFont();
         presentation.addStyleRange(styleRange);
      }
   }
}
