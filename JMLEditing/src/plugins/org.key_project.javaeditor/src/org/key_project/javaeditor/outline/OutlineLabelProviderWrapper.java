package org.key_project.javaeditor.outline;

import org.eclipse.jdt.internal.ui.viewsupport.DecoratingJavaLabelProvider;
import org.eclipse.jdt.internal.ui.viewsupport.JavaUILabelProvider;
import org.eclipse.swt.graphics.Image;

/**
 * Wrapper to Extend {@link DecoratingJavaLabelProvider} to extend the Outline.
 * @author Timm Lippert
 * @see IOutlineImageProvider
 */
@SuppressWarnings("restriction")
public class OutlineLabelProviderWrapper extends DecoratingJavaLabelProvider {
   /**
    * Constructor.
    * @param labelProvider The label provider to decorate.
    */
   public OutlineLabelProviderWrapper(JavaUILabelProvider labelProvider) {
      super(labelProvider);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final Image getImage(Object element) {
      if (element instanceof IOutlineImageProvider) {
         return ((IOutlineImageProvider) element).getImage();
      }
      else {
         return super.getImage(element);
      }
   }
}
