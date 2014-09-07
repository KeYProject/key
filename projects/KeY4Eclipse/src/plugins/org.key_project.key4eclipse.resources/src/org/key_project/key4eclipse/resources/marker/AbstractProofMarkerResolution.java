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
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IMarkerResolution2;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

/**
 * Provides the QuickFixes for the KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public abstract class AbstractProofMarkerResolution implements IMarkerResolution2 {
   /**
    * The label to show.
    */
   private final String label;
   
   /**
    * The description to show.
    */
   private final String description;
   
   /**
    * Initializes the global variables depending on the given {@link IMarker#getType()}.
    * @param marker - the given {@link IMarker}
    * @throws CoreException 
    */
   public AbstractProofMarkerResolution(IMarker marker) throws CoreException {
      IFile proofFile = KeYResourcesUtil.getProofFile(marker);
      String proofFileName = proofFile.getName();
      if (MarkerManager.CLOSEDMARKER_ID.equals(marker.getType())) {
         description = getClosedMarkerDescriptionPrefix() + proofFileName;
      }
      else if (MarkerManager.NOTCLOSEDMARKER_ID.equals(marker.getType())) {
         description = getNotClosedMarkerDescriptionPrefix() + proofFileName;
      }
      else {
         description = null;
      }
      this.label = getLabelPrefix() + proofFileName;
   }
   
   /**
    * Returns the closed marker description prefix.
    * @return The closed marker description prefix.
    */
   protected abstract String getClosedMarkerDescriptionPrefix();

   /**
    * Returns the not closed marker description prefix.
    * @return The not closed marker description prefix.
    */
   protected abstract String getNotClosedMarkerDescriptionPrefix();

   /**
    * Returns the label prefix.
    * @return The label prefix.
    */
   protected abstract String getLabelPrefix();

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
         IFile file = KeYResourcesUtil.getProofFile(marker);
         run(marker, file);
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(null, e);
      }
   }
   
   protected abstract void run(IMarker marker, IFile proofFile) throws Exception;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return description;
   }
}