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
import org.eclipse.swt.graphics.Image;
import org.key_project.key4eclipse.common.ui.util.KeYImages;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;

/**
 * Provides the QuickFixes for the KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public class ProofMarkerResolution extends AbstractProofMarkerResolution {
   /**
    * Initializes the global variables depending on the given {@link IMarker#getType()}.
    * @param marker - the given {@link IMarker}
    * @throws CoreException 
    */
   public ProofMarkerResolution(IMarker marker) throws CoreException {
      super(marker);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getClosedMarkerDescriptionPrefix() {
      return "Open proof: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getNotClosedMarkerDescriptionPrefix() {
      return "Open proof to close it manually: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getLabelPrefix() {
      return "Open proof: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return KeYImages.getImage(KeYImages.KEY_LOGO);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void run(IMarker marker, IFile proofFile) throws Exception {
      StarterUtil.openFileStarter(null, proofFile);
   }
}