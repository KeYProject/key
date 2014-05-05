/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.resources.marker;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMarkerResolution2;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Provides the QuickFixes for the KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public class ProofMarkerResolution implements IMarkerResolution2{

   private String label;
   private String description;
   private boolean openInKeY;
   
   /**
    * Initializes the global variables depending on the given {@link IMarker#getType()}.
    * @param marker - the given {@link IMarker}
    * @throws CoreException 
    */
   public ProofMarkerResolution(IMarker marker) throws CoreException {
      IFile proofFile = getProofFile(marker);
      String proofFileName = proofFile.getFullPath().lastSegment();
      if(MarkerManager.CLOSEDMARKER_ID.equals(marker.getType())){
         description = "Open proof: " + proofFileName;
      }
      else if(MarkerManager.NOTCLOSEDMARKER_ID.equals(marker.getType())){
         description = "Open proof to close it manually: " + proofFileName;
      }
      this.label = "Open proof: " + proofFileName;
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
         IFile file = getProofFile(marker);
         if(!openInKeY){
            StarterUtil.openFileStarter(null, file);
         }
         else{
            KeYUtil.loadAsync(file);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
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
      String str = (String) marker.getAttribute(IMarker.SOURCE_ID);
      IPath proofFilePath = new Path(str);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile proofFile = root.getFile(proofFilePath);
      return proofFile;
   }
}