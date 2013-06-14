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

package org.key_project.key4eclipse.common.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;

/**
 * Handler to start a proof for selected {@link IProject}s via
 * {@link StarterUtil#openProjectStarter(Shell, IProject)}.
 */
public class ProjectStarterHandler extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      Shell parentShell = HandlerUtil.getActiveShell(event);
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      if (selection instanceof IStructuredSelection) {
         // Try to load by selection
         Object[] elements = ((IStructuredSelection) selection).toArray();
         for (Object element : elements) {
            if (element instanceof IResource) {
               IProject project = ((IResource)element).getProject();
               StarterUtil.openProjectStarter(parentShell, project);
            }
            else if (element instanceof IJavaElement) {
               IJavaElement javaElement = (IJavaElement) element;
               IProject project = javaElement.getResource().getProject();
               StarterUtil.openProjectStarter(parentShell, project);
            }
         }
      }
      else {
         // Try to load by KeY Editor
         IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
         if (editorPart != null) {
            IEditorInput input = editorPart.getEditorInput();
            if (input != null) {
               IFile file = (IFile) input.getAdapter(IFile.class);
               if (file != null) {
                  StarterUtil.openProjectStarter(parentShell, file.getProject());
               }
            }
         }
      }
      return null;
   }
}