package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.IJavaElement;

public class DefaultOutlineModifiyer implements IOutlineModifier {
   @Override
   public IJavaElement[] modify(IJavaElement parent, IJavaElement[] currentChildren) {
      return currentChildren;
   }
}
