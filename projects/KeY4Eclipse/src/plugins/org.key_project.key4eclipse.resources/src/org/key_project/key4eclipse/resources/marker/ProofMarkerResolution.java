package org.key_project.key4eclipse.resources.marker;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMarkerResolution2;
import org.key_project.key4eclipse.resources.util.KeY4EclipseResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

public class ProofMarkerResolution implements IMarkerResolution2{

   private String label;
   private String description;
   private String openIn;

   
   /**
    * Initializes the global variables depending on the given {@link IMarker#getType()}.
    * @param markerType - the given {@link IMarker#getType()}
    * @param openIn
    */
   public ProofMarkerResolution(String markerType, String openIn){
      if(markerType.equals(MarkerManager.CLOSEDMARKER_ID)){
         description = "Open the proof in KeY";
      }
      else if(markerType.equals(MarkerManager.NOTCLOSEDMARKER_ID)){
         description = "Open the proof in KeY to close it manually";
      }
      this.openIn = openIn;
      if(openIn.equals("KeY")){
         label = "Open proof in KeY";
      }
      else if(openIn.equals("KeYIDE")){
         label = "Open proof in KeY-Editor";
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getLabel() {
      return label;
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IMarker marker) {
      try {
         if(openIn.equals("KeY")){
            IFile file= getProofFile(marker);
            KeYUtil.loadAsync(file);
         }
         else if(openIn.equals("KeYIDE")){
            IFile file= getProofFile(marker);
            File proofFile = file.getLocation().toFile();
            KeY4EclipseResourcesUtil.openProofFileInKeYIDE(proofFile);
         }
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
      return description;
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return null;
   }
   
   private IFile getProofFile(IMarker marker) throws CoreException{
      StringBuffer sb = new StringBuffer((String) marker.getAttribute(IMarker.MESSAGE));
      if(marker.getType().equals(MarkerManager.CLOSEDMARKER_ID)){
         sb.delete(0, 15);
      }
      else if(marker.getType().equals(MarkerManager.NOTCLOSEDMARKER_ID)){
         sb.delete(0, 19);
      }
      IPath proofFilePath = new Path(sb.toString());
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile proofFile = root.getFile(proofFilePath);
      return proofFile;
   }
}

   