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

import java.util.LinkedList;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

/**
 * Creates the QuickFixes for the KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public class ProofMarkerResolutionGenerator implements IMarkerResolutionGenerator {

   
   /**
    * {@inheritDoc}
    */
   @Override
   public IMarkerResolution[] getResolutions(IMarker marker) {
      LinkedList<IMarkerResolution> resolutions = new LinkedList<IMarkerResolution>();
      try{
         if (StarterUtil.areFileStartersAvailable()) {
            resolutions.add(new ProofMarkerResolution(marker.getType(), false));
            resolutions.add(new ProofMarkerResolution(marker.getType(), true));
         }
      } catch (CoreException e){
         LogUtil.getLogger().createErrorStatus(e); // TODO: You do nothing with the created status. I guess you mean LogUtil.getLogger().logError(e); which writes the exception into the eclipse log
      }
      return (IMarkerResolution[])resolutions.toArray(new IMarkerResolution[resolutions.size()]);
   }
}