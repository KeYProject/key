package org.key_project.sed.key.ui.marker;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;
import org.key_project.key4eclipse.resources.marker.AbstractProofMarkerResolution;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.ui.launch.KeYLaunchShortcut;
import org.key_project.sed.ui.util.SEDImages;

/**
 * Launches a proof file for debugging purpose in the Symbolic Execution Debugger (SED).
 * @author Martin Hentschel
 */
public class DebugProofMarkerResolution extends AbstractProofMarkerResolution {
   /**
    * Constructor.
    * @param marker The {@link IMarker} to handle.
    * @throws CoreException Occurred Exception
    */
   public DebugProofMarkerResolution(IMarker marker) throws CoreException {
      super(marker);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getClosedMarkerDescriptionPrefix() {
      return "Debug proof: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getNotClosedMarkerDescriptionPrefix() {
      return "Debug proof: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getLabelPrefix() {
      return "Debug proof: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return SEDImages.getImage(SEDImages.SYMBOLIC_DEBUG);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void run(IMarker marker, IFile proofFile) throws Exception {
      KeYLaunchShortcut.launch(proofFile, KeySEDUtil.MODE);
   }
}
