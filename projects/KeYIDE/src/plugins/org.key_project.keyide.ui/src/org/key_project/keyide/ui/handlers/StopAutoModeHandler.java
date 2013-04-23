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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.editor.IProofEnvironmentProvider;

// TODO: Document class StopAutoModeHandler
public class StopAutoModeHandler extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      if (editorPart != null) {
         IProofEnvironmentProvider proofProvider = (IProofEnvironmentProvider)editorPart.getAdapter(IProofEnvironmentProvider.class);
         if (proofProvider != null && proofProvider.getKeYEnvironment().getMediator().autoMode()) {
            proofProvider.getKeYEnvironment().getUi().stopAutoMode();
         }
      }
      return null;
   }
}