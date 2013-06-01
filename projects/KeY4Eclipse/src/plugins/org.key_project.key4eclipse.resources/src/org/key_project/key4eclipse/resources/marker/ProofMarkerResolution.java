/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

public class ProofMarkerResolution implements IMarkerResolution2{

   private String label;
   private String description;

   
   /**
    * Initializes the global variables depending on the given {@link IMarker#getType()}.
    * @param markerType - the given {@link IMarker#getType()}
    */
   public ProofMarkerResolution(String markerType) {
      if(markerType.equals(MarkerManager.CLOSEDMARKER_ID)){
         description = "Open Proof";
      }
      else if(markerType.equals(MarkerManager.NOTCLOSEDMARKER_ID)){
         description = "Open Proof to close it manually";
      }
      this.label = "Open Proof";
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
         StarterUtil.openFileStarter(null, file);
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