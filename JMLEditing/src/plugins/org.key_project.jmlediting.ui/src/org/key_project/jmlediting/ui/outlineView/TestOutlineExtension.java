package org.key_project.jmlediting.ui.outlineView;

import org.eclipse.jdt.core.IJavaElement;
import org.key_project.javaeditor.outline.DefaultOutlineModifiyer;
import org.key_project.javaeditor.outline.NoRealJavaElement;

public class TestOutlineExtension extends DefaultOutlineModifiyer {
   @Override
   public Object[] modify(Object parent, Object[] currentChildren) {
      if (currentChildren.length >= 1 && currentChildren[0] instanceof IJavaElement) {
         Object[] newChildren = new Object[currentChildren.length + 2];
         System.arraycopy(currentChildren, 0, newChildren, 0, currentChildren.length);
         IJavaElement firstChild = (IJavaElement) currentChildren[0];
         newChildren[currentChildren.length] = new NoRealJavaElement(firstChild.getJavaProject(), "Hello World");
         newChildren[currentChildren.length + 1] = new NoRealJavaElement(firstChild.getJavaProject(), "Achtung");
         return newChildren;
      }
      else {
         return currentChildren;
      }
   }
}
