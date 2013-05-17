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

package org.key_project.key4eclipse.starter.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Handler that loads selected {@link IFile}s if supported 
 * in the KeY UI via {@link KeYUtil#loadAsync(IResource)}.
 */
public class LoadResourceHandler extends AbstractSaveExecutionHandler {
    /**
     * {@inheritDoc}
     */
    @Override
    protected Object doExecute(ExecutionEvent event) throws Exception {
        ISelection selection = HandlerUtil.getCurrentSelection(event);
        if (selection instanceof IStructuredSelection) {
            // Try to load by selection
            Object[] elements = ((IStructuredSelection)selection).toArray();
            for (Object element : elements) {
                if (element instanceof IResource) {
                    KeYUtil.loadAsync((IResource)element);
                }
                else if (element instanceof IJavaElement) {
                    KeYUtil.loadAsync(((IJavaElement)element).getResource());
                }
            }
        }
        else {
            // Try to load by KeY Editor
            IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
            if (editorPart != null) {
                IEditorInput input = editorPart.getEditorInput();
                if (input != null) {
                    IFile file = (IFile)input.getAdapter(IFile.class);
                    if (file != null && 
                        KeYUtil.isFileExtensionSupported(file.getFileExtension())) {
                        KeYUtil.loadAsync(file);
                    }
                }
            }
        }
        return null;
    }
}