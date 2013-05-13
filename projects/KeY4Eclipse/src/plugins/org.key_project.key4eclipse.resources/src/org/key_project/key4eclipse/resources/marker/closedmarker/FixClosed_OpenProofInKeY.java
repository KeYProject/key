package org.key_project.key4eclipse.resources.marker.closedmarker;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMarkerResolution2;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

public class FixClosed_OpenProofInKeY implements IMarkerResolution2{

   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getLabel() {
      return "Open proof in KeY";
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IMarker marker) {
      try {
         IPath proofPath = (IPath) marker.getAttribute(IMarker.TEXT);
         IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
         IFile file= root.getFile(proofPath);
         KeYUtil.loadAsync(file);
      }
      catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return "Open the proof in KeY";
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return null;
   }
}
