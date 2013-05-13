package org.key_project.key4eclipse.resources.marker.notclosedmarker;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMarkerResolution2;
import org.key_project.key4eclipse.resources.util.KeY4EclipseResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

public class FixNotClosed_OpenProofInKeYIDE implements IMarkerResolution2{

   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getLabel() {
      return "Open proof in KeY-Editor";
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
         File proofFile = file.getLocation().toFile();
         IProject project = marker.getResource().getProject();
         KeY4EclipseResourcesUtil.openProofFileInKeYIDE(proofFile, project);
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
      return "Open the proof in a KeY-Editor in Eclipse to close it manually";
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return null;
   }
}