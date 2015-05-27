package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.IJavaElement;

/**
 * Implementations of this class wrapp an existing {@link IJavaElement} to
 * change its content shown in the outline view.
 * @author Martin Hentschel
 * @param <J> The type of the wrapped {@link IJavaElement}.
 */
public interface IOutlineWrapper<J extends IJavaElement> {
   /**
    * Returns the wrapped {@link IJavaElement}.
    * @return The wrapped {@link IJavaElement}.
    */
   public J getWrappedObject();
}
