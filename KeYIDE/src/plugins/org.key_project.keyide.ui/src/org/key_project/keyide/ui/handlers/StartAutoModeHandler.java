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

package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.keyide.ui.job.AbstractKeYEnvironmentJob;

import de.uka.ilkd.key.proof.Proof;

/**
 * This {@link IHandler} starts the auto mode of the currently active
 * {@link IProofProvider}.
 * @author Martin Hentschel
 */
public class StartAutoModeHandler extends AbstractSaveExecutionHandler {   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      startAutoMode(editorPart);
      return null;
   }

   /**
    * Starts the auto mode in case the given {@link IWorkbenchPart} is a {@link IProofProvider}.
    * @param workbenchPart The {@link IWorkbenchPart} to treat.
    */
   public static void startAutoMode(IWorkbenchPart workbenchPart) {
      final IProofProvider proofProvider;
      if (workbenchPart instanceof IProofProvider) {
         proofProvider = (IProofProvider) workbenchPart;
      }
      else if (workbenchPart != null) {
         proofProvider = (IProofProvider) workbenchPart.getAdapter(IProofProvider.class);
      }
      else {
         proofProvider = null;
      }
      if (proofProvider != null) {
         final Proof proof = proofProvider.getCurrentProof();
         if (proof != null &&
             proofProvider.getProofControl().isAutoModeSupported(proof) && 
             !proofProvider.getProofControl().isInAutoMode()) {
            new AbstractKeYEnvironmentJob("Auto Mode", proofProvider.getEnvironment()) {
               // job that starts the automode in KeY
               @Override
               protected IStatus run(IProgressMonitor monitor) {
                  monitor.beginTask("Proving with KeY", IProgressMonitor.UNKNOWN);
                  proof.getActiveStrategy(); // Make sure that the strategy is initialized correctly, otherwise the used settings are different to the one defined by the strategysettings which are shown in the UI.
                  proofProvider.getProofControl().startAndWaitForAutoMode(proof);
                  monitor.done();
                  return Status.OK_STATUS;
               }
            }.schedule();
         }
      }
   }
}