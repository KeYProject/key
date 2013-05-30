package org.key_project.key4eclipse.resources.marker;

import java.util.LinkedList;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;
import org.key_project.key4eclipse.resources.util.LogUtil;

public class ProofMarkerResolutionGenerator implements IMarkerResolutionGenerator {

   
   /**
    * {@inheritDoc}
    */
   @Override
   public IMarkerResolution[] getResolutions(IMarker marker) {
      LinkedList<IMarkerResolution> resolutions = new LinkedList<IMarkerResolution>();
      try{
         resolutions.add(new ProofMarkerResolution(marker.getType(), "KeY"));
         resolutions.add(new ProofMarkerResolution(marker.getType(), "KeYIDE"));
      } catch (CoreException e){
         LogUtil.getLogger().createErrorStatus(e);
      }
      return (IMarkerResolution[])resolutions.toArray(new IMarkerResolution[resolutions.size()]);
   }
}
