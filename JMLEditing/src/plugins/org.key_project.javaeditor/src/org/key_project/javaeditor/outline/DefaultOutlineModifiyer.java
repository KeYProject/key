package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.ElementChangedEvent;
import org.eclipse.jdt.internal.ui.javaeditor.JavaOutlinePage;

/**
 * Default Implementation of the {@link IOutlineModifier} which changes nothing in the Outline.
 * @author Timm Lippert
 */
@SuppressWarnings("restriction")
public class DefaultOutlineModifiyer implements IOutlineModifier {
   @Override
   public final Object[] modify(Object parent, Object[] currentChildren, JavaOutlinePage javaOutlinePage) {
      return currentChildren;
   }

   @Override
   public void changeDetected(ElementChangedEvent event) {
   }
}
