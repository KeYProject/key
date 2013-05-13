package org.key_project.key4eclipse.resources.marker.closedmarker;

import java.util.LinkedList;

import org.eclipse.core.resources.IMarker;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;

public class ProofClosedMarkerQuickFix implements IMarkerResolutionGenerator {

   
   /**
    * {@inheritDoc}
    */
   @Override
   public IMarkerResolution[] getResolutions(IMarker marker) {
      LinkedList<IMarkerResolution> resolutions = new LinkedList<IMarkerResolution>();
      resolutions.add(new FixClosed_OpenProofInKeYIDE());
      resolutions.add(new FixClosed_OpenProofInKeY());
      return (IMarkerResolution[])resolutions.toArray(new IMarkerResolution[resolutions.size()]);
   }
}
