package org.key_project.key4eclipse.resources.marker.notclosedmarker;

import java.util.LinkedList;

import org.eclipse.core.resources.IMarker;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;

public class ProofNotClosedMarkerQuickFix implements IMarkerResolutionGenerator {

   
   /**
    * {@inheritDoc}
    */
   @Override
   public IMarkerResolution[] getResolutions(IMarker marker) {
      LinkedList<IMarkerResolution> resolutions = new LinkedList<IMarkerResolution>();
      resolutions.add(new FixNotClosed_OpenProofInKeYIDE());
      resolutions.add(new FixNotClosed_OpenProofInKeY());
      return (IMarkerResolution[])resolutions.toArray(new IMarkerResolution[resolutions.size()]);
   }
}
