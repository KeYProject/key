package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.ElementChangedEvent;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.internal.ui.javaeditor.JavaOutlinePage;

/**
 * Interface for extension for the standard Java outline.
 * @author Timm Lippert
 */
@SuppressWarnings("restriction")
public interface IOutlineModifier {
   /**
    * Method to extend the standard Outline and adds the returning children to to the parent
    * element.
    * 
    * @param parent The current parent {@link IJavaElement} which children can be modified.
    * @param currentChildren All children the current parent {@link IJavaElement} contains.
    * @param javaOutlinePage The {@link JavaOutlinePage} in which {@link #originalProvider} and this instance is used.
    * @return All children that should be as child under the parent {@link IJavaElement}.
    */
   public Object[] modify(Object parent, Object[] currentChildren, JavaOutlinePage javaOutlinePage);
   
   /**
    * When a change is detected.
    * @param event The {@link ElementChangedEvent}.
    */
   public void changeDetected(ElementChangedEvent event);
}
