package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.IJavaElement;

/**
 * Interface for extension for the standart Java outline
 * @author Timm Lippert
 *
 */


public interface IOutlineModifier {
   
   /**
    *  Method to Extend the standart Outline and adds the returning Children to to the Parent Element
    *  
    * @param parent The current parent {@link IJavaElement} which children can be modified
    * @param currentChildren  All Children the current parent {@link IJavaElement} contains
    * @return All children that should be as Child under the parent {@link IJavaElement}
    */
   public Object[] modify(Object parent, Object[] currentChildren);
}
