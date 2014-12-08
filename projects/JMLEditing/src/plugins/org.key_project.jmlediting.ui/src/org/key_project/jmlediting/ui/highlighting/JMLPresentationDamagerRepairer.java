package org.key_project.jmlediting.ui.highlighting;

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
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.util.JML_UIPreferencesHelper;
import org.key_project.util.eclipse.WorkbenchUtil;

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
      final RGB jmlColor = JML_UIPreferencesHelper
            .getActiveJMLColor(WorkbenchUtil.getCurrentProject());
      final RGB defaultJMLColor = JML_UIPreferencesHelper.getDefaultJMLColor();
      final CommentLocator locator = new CommentLocator(this.doc.get());
      jml = locator.isInJMLcomment(damage.getOffset());
      final TextAttribute ta;
      if (jml) {
         if (jmlColor != null) {
            ta = new TextAttribute(new Color(Display.getDefault(),
                  jmlColor.red, jmlColor.green, jmlColor.blue));
         }
         else {
            ta = new TextAttribute(new Color(Display.getDefault(),
                  defaultJMLColor.red, defaultJMLColor.green,
                  defaultJMLColor.blue));
         }
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
      final CommentLocator locator = new CommentLocator(this.doc.get());
      final CommentRange surComment = locator.getCommentOfOffset(event
            .getOffset());
      if (surComment == null) {
         return damage;
      }
      int eventLine = 0;
      int commentLine = 0;
      try {
         eventLine = this.doc.getLineOfOffset(event.getOffset());
         commentLine = this.doc.getLineOfOffset(surComment.getBeginOffset());
      }
      catch (final BadLocationException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      if (eventLine == commentLine) {
         return new Region(surComment.getBeginOffset(),
               surComment.getEndOffset() - surComment.getBeginOffset() + 1);
      }

      return damage;
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
