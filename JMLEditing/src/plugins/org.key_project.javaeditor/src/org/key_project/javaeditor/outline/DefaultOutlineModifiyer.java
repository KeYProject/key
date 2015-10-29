package org.key_project.javaeditor.outline;

/**
 * Default Implementation of the {@link IOutlineModifier} which changes nothing in the
 * Outline.
 *
 * @author Timm Lippert
 *
 */
public class DefaultOutlineModifiyer implements IOutlineModifier {

   public final Object[] modify(Object parent, Object[] currentChildren) {
      return currentChildren;
   }
}
