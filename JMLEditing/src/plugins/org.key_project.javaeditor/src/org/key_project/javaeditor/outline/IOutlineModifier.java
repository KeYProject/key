package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.IJavaElement;

public interface IOutlineModifier {
   public IJavaElement[] modify(IJavaElement parent, IJavaElement[] currentChildren);
}
