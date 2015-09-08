package org.key_project.javaeditor.outline;

/**
 * Default Implementation of the {@link IOutlineModifier} which changes nothing in the Outline.
 * Override to implement a different behavior.
 *
 * @author Timm Lippert
 *
 */

public class DefaultOutlineModifiyer implements IOutlineModifier {
   
   public Object[] modify(Object parent, Object[] currentChildren) {
      return currentChildren;
   }
}
