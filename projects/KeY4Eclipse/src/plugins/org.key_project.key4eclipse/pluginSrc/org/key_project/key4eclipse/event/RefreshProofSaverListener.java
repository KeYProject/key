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

package org.key_project.key4eclipse.event;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.key_project.key4eclipse.Activator;

import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.io.event.ProofSaverEvent;
import de.uka.ilkd.key.proof.io.event.ProofSaverListener;

/**
 * This {@link ProofSaverListener} refreshes the {@link IFile}s when
 * a proof was saved by a {@link ProofSaver}.
 * @author Martin Hentschel
 */
public class RefreshProofSaverListener implements ProofSaverListener {
   /**
    * {@inheritDoc}
    */
   @Override
   public void proofSaved(ProofSaverEvent e) {
      try {
         File savedFile = new File(e.getFilename());
         IFile[] files = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(savedFile.toURI());
         if (files != null) {
            for (IFile file : files) {
               file.refreshLocal(IResource.DEPTH_INFINITE, null);
            }
         }
      }
      catch (CoreException exc) {
         Activator.getDefault().getLog().log(new Status(IStatus.ERROR, Activator.PLUGIN_ID, exc.getMessage(), exc));
      }
   }
}