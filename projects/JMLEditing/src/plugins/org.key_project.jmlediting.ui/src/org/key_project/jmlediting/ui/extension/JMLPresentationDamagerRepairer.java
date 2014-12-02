package org.key_project.jmlediting.ui.extension;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
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

   /**
    * @return the original DamageRegion when the DamageOffset is not done in the
    *         First Line of a Comment if the Damage Offset is in the first Line
    *         of a Comment the whole Comment has to be Redisplayed which results
    *         in an extension of the Damage Region to the whole Comment
    */
   @Override
   public IRegion getDamageRegion(final ITypedRegion partition,
         final DocumentEvent event, final boolean documentPartitioningChanged) {
      final IRegion damage = this.wrappedInstance.getDamageRegion(partition,
            event, documentPartitioningChanged);
      final JMLLocator locator = new JMLLocator(this.doc.get());
      final Comment surComment = locator.getCommentOfOffset(event.getOffset());
      if (surComment == null) {
         return damage;
      }
      int eventLine = 0;
      int commentLine = 0;
      try {
         eventLine = this.doc.getLineOfOffset(event.getOffset());
         commentLine = this.doc.getLineOfOffset(surComment.getOffset());
      }
      catch (final BadLocationException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      if (eventLine == commentLine) {
         return new Region(surComment.getOffset(), surComment.getEnd()
               - surComment.getOffset() + 1);
      }

      return null;
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
