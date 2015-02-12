package org.key_project.sed.key.ui.marker;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;
import org.key_project.key4eclipse.resources.util.LogUtil;

/**
 * Provides the option to debug a proof file in the Symbolic Execution Debugger (SED).
 * @author Martin Hentschel
 */
public class SEDProofMarkerResolutionGenerator implements IMarkerResolutionGenerator {
   /**
    * {@inheritDoc}
    */
   @Override
   public IMarkerResolution[] getResolutions(IMarker marker) {
      try {
         return new IMarkerResolution[] {new DebugProofMarkerResolution(marker)};
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         return new IMarkerResolution[0];
      }
   }
}
