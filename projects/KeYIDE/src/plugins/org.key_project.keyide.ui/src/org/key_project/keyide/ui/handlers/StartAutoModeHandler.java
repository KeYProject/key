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

package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.keyide.ui.job.AbstractKeYEnvironmentJob;

// TODO: Document class StartAutoModeHandler
public class StartAutoModeHandler extends AbstractSaveExecutionHandler {   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      //initialize values for execution
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      if (editorPart != null) {
         final IProofProvider proofProvider = (IProofProvider)editorPart.getAdapter(IProofProvider.class);
         if (proofProvider != null && 
             proofProvider.getEnvironment().getUi().isAutoModeSupported(proofProvider.getCurrentProof()) && 
             !proofProvider.getEnvironment().getMediator().autoMode()) {
            new AbstractKeYEnvironmentJob("Auto Mode", proofProvider.getEnvironment()) {
               // job that starts the automode in KeY
               @Override
               protected IStatus run(IProgressMonitor monitor) {
                  monitor.beginTask("Proving with KeY", IProgressMonitor.UNKNOWN);
                  proofProvider.getCurrentProof().getActiveStrategy(); // Make sure that the strategy is initialized correctly, otherwise the used settings are different to the one defined by the strategysettings which are shown in the UI.
                  proofProvider.getEnvironment().getUi().startAndWaitForAutoMode(proofProvider.getCurrentProof());
                  monitor.done();
                  return Status.OK_STATUS;
               }
            }.schedule();
         }
      }
      return null;
   }
}
