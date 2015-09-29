package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.internal.ui.viewsupport.DecoratingJavaLabelProvider;
import org.eclipse.jdt.internal.ui.viewsupport.JavaUILabelProvider;
import org.eclipse.swt.graphics.Image;

/**
 * Wrapper to Extend {@link DecoratingJavaLabelProvider} to extend the Outline.
 * 
 * @author Timm Lippert
 *
 */
@SuppressWarnings("restriction")
public class OutlineLableWrapper extends DecoratingJavaLabelProvider {

   public OutlineLableWrapper(JavaUILabelProvider labelProvider) {
      super(labelProvider);
   }

   @Override
   public final Image getImage(Object element) {
      if (((IJavaElement) element).getElementType() == 100) {
         return OutlineJMLPicture.getimage();
      }
      else
         return super.getImage(element);
   }
}
