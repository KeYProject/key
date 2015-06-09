package org.key_project.javaeditor.outline;

public class DefaultOutlineModifiyer implements IOutlineModifier {
   @Override
   public Object[] modify(Object parent, Object[] currentChildren) {
      return currentChildren;
   }
}
