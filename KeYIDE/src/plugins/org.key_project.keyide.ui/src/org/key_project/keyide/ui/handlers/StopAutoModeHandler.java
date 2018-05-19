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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;

/**
 * This {@link IHandler} stops the auto mode of the currently active
 * {@link IProofProvider}.
 * @author Martin Hentschel
 */
public class StopAutoModeHandler extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      stopAutoMode(editorPart);
      return null;
   }
   
   /**
    * Stops the auto mode of the given {@link IWorkbenchPart}.
    * @param workbenchPart The {@link IWorkbenchPart} to treat.
    */
   public static void stopAutoMode(IWorkbenchPart workbenchPart) {
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
      if (proofProvider != null && proofProvider.getProofControl().isInAutoMode()) {
         proofProvider.getProofControl().stopAutoMode();
      }
   }
}