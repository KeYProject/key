package org.key_project.sed.core.slicing;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.annotation.impl.SliceAnnotation;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Defines the functionality to perform slicing.
 * @author Martin Hentschel
 */
public interface ISEDSlicer {
   /**
    * Returns the name of the slicing algorithm.
    * @return The name of the slicing algorithm.
    */
   public String getName();
   
   /**
    * Performs the slicing.
    * @param seedNode The seed {@link ISEDDebugNode}.
    * @param seedVariable The seed {@link IVariable}.
    * @return The {@link SliceAnnotation} representing the computed slice.
    * @throws DebugException Occurred Exception.
    */
   public SliceAnnotation slice(ISEDDebugNode seedNode, IVariable seedVariable) throws DebugException;
}
