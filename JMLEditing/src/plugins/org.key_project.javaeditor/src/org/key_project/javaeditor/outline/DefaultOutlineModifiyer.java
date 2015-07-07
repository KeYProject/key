package org.key_project.javaeditor.outline;

/**
 * Default Implementation of the {@link IOutlineModifier} to be Override which changes nothing in the Outline
 *
 * @author Timm Lippert
 *
 */

public class DefaultOutlineModifiyer implements IOutlineModifier {
   @Override
   public Object[] modify(Object parent, Object[] currentChildren) {
      return currentChildren;
   }
}
