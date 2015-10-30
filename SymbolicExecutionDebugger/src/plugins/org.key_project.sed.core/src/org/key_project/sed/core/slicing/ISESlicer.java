package org.key_project.sed.core.slicing;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.annotation.ISEAnnotationAppearance;
import org.key_project.sed.core.annotation.impl.SliceAnnotation;
import org.key_project.sed.core.model.ISENode;

/**
 * Defines the functionality to perform slicing.
 * @author Martin Hentschel
 */
public interface ISESlicer {
   /**
    * Returns the name of the slicing algorithm.
    * @return The name of the slicing algorithm.
    */
   public String getName();
   
   /**
    * Performs the slicing.
    * @param seedNode The seed {@link ISENode}.
    * @param seedVariable The seed {@link IVariable}.
    * @param appearance An optional {@link ISEAnnotationAppearance} specific how the created {@link SliceAnnotation} should look like.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The {@link SliceAnnotation} representing the computed slice.
    * @throws DebugException Occurred Exception.
    */
   public SliceAnnotation slice(ISENode seedNode, 
                                IVariable seedVariable, 
                                ISEAnnotationAppearance appearance,
                                IProgressMonitor monitor) throws DebugException;
}
