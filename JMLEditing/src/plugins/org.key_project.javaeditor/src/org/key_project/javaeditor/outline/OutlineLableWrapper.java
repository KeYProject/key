package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.hierarchy.IndexBasedHierarchyBuilder;
import org.eclipse.jdt.internal.ui.text.JavaOutlineInformationControl;
import org.eclipse.jdt.internal.ui.viewsupport.AppearanceAwareLabelProvider;
import org.eclipse.jdt.internal.ui.viewsupport.DecoratingJavaLabelProvider;
import org.eclipse.jdt.internal.ui.viewsupport.JavaUILabelProvider;
import org.eclipse.jdt.ui.JavaElementLabels;
import org.eclipse.jface.viewers.DecoratingLabelProvider;
import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.ILabelDecorator;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Shell;

/**
 * Wrapper to Extend {@link DecoratingJavaLabelProvider} to extend the Outline
 * 
 * @author Timm Lippert
 *
 */
@SuppressWarnings("restriction")
public class OutlineLableWrapper extends DecoratingJavaLabelProvider  {




   public OutlineLableWrapper(JavaUILabelProvider labelProvider) {
      super(labelProvider);
      // TODO Auto-generated constructor stub
   }

   @Override
   public Image getImage(Object element) {
      if(((IJavaElement) element).getElementType() == 100){
         return OutlineJMLPicture.getimage();
      }else
      return super.getImage(element);
   }
}
