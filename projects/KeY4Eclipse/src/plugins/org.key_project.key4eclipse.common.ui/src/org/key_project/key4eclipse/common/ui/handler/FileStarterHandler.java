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

package org.key_project.key4eclipse.common.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Handler to start a proof for selected {@link IFile}s via
 * {@link StarterUtil#openFileStarter(Shell, IFile)}.
 */
public class FileStarterHandler extends AbstractSaveExecutionHandler {
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
            if (element instanceof IFile) {
               IFile file = (IFile)element;
               if (KeYUtil.isFileExtensionSupported(file.getFileExtension())) {
                  StarterUtil.openFileStarter(parentShell, file);
               }
            }
            else if (element instanceof IJavaElement) {
               IJavaElement javaElement = (IJavaElement) element;
               if (javaElement.getResource() instanceof IFile) {
                  IFile file = (IFile)javaElement.getResource();
                  if (KeYUtil.isFileExtensionSupported(file.getFileExtension())) {
                     StarterUtil.openFileStarter(parentShell, file);
                  }
               }
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
               if (file != null && KeYUtil.isFileExtensionSupported(file.getFileExtension())) {
                  StarterUtil.openFileStarter(parentShell, file);
               }
            }
         }
      }
      return null;
   }
}