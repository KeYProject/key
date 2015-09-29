package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.IJavaElement;

/**
 * Interface for extension for the standard Java outline.
 * 
 * @author Timm Lippert
 *
 */
public interface IOutlineModifier {

   /**
    * Method to extend the standard Outline and adds the returning children to to the parent
    * element.
    * 
    * @param parent The current parent {@link IJavaElement} which children can be modified.
    * @param currentChildren All children the current parent {@link IJavaElement} contains.
    * @return All children that should be as child under the parent {@link IJavaElement}.
    */
   public Object[] modify(Object parent, Object[] currentChildren);
}
