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

package org.key_project.sed.key.ui.launch;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.ILaunchShortcut;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.ui.util.LaunchUIUtil;

import de.uka.ilkd.key.java.Position;

/**
 * {@link ILaunchShortcut} implementation for Symbolic Executiong Debugger
 * based on KeY.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYLaunchShortcut implements ILaunchShortcut {
    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(ISelection selection, String mode) {
        try {
            if (selection instanceof IStructuredSelection && !selection.isEmpty()) {
                Object element = ((IStructuredSelection)selection).getFirstElement();
                if (element instanceof IMethod) {
                    launch((IMethod)element, mode, null, null);
                }
                else if (element instanceof IFile) {
                   launch((IFile)element, mode);
                }
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(null, e);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(IEditorPart editor, String mode) {
        try {
            if (editor instanceof JavaEditor) {
                JavaEditor javaEditor = (JavaEditor)editor;
                if (javaEditor.getSelectionProvider() != null) {
                    ISelection selection = javaEditor.getSelectionProvider().getSelection();
                    if (selection instanceof ITextSelection) {
                        ITextSelection textSelection = (ITextSelection)selection;
                        IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, textSelection);
                        if (element instanceof IMethod) {
                            IMethod method = (IMethod)element;
                            // Check if a range in the method is selected or if the complete method should be executed (only its name or part of it is selected)
                            if (textSelection.getOffset() >= method.getNameRange().getOffset() &&
                                textSelection.getOffset() + textSelection.getLength() <= method.getNameRange().getOffset() + method.getNameRange().getLength()) {
                                // Execute only method
                                launch(method, mode, null, null);
                            }
                            else {
                                // Compute positions of selected code
                                Position methodStartPosition = KeYUtil.getCursorPositionForOffset(method, textSelection.getOffset());
                                Position methodEndPosition = KeYUtil.getCursorPositionForOffset(method, textSelection.getOffset() + textSelection.getLength());
                                launch(method, mode, methodStartPosition, methodEndPosition);
                            }
                        }
                    }
                }
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(null, e);
        }
    }
    
    /**
     * Launches the given {@link IFile}.
     * @param file The {@link IFile} to launch.
     * @param mode The mode to use.
     * @throws CoreException Occurred Exception.
     */
    public static void launch(IFile file, 
                              String mode) throws CoreException {
        try {
            ILaunchConfiguration config = findLaunchConfiguration(file);
            if (config == null) {
                config = KeySEDUtil.createConfiguration(file);
            }
            if (config != null) {
                DebugUITools.launch(config, mode);
            }
        }
        catch (OperationCanceledException e) {
            // Nothing to do
        }
    }
    
    /**
     * Tries to find an existing {@link ILaunchConfiguration} for the
     * given {@link IFile}. If multiple {@link ILaunchConfiguration} exists
     * the user is asked to select one.
     * @param file The {@link IFile} for that an {@link ILaunchConfiguration} is needed.
     * @return The found {@link ILaunchConfiguration} or {@code null} if no one was found.
     * @throws CoreException Occurred Exception.
     * @throws OperationCanceledException When the user has canceled the select dialog.
     */
    public static ILaunchConfiguration findLaunchConfiguration(IFile file) throws CoreException {
        List<ILaunchConfiguration> candidateConfigs = KeySEDUtil.searchLaunchConfigurations(file);
        int candidateCount = candidateConfigs.size();
        if (candidateCount == 1) {
            return (ILaunchConfiguration)candidateConfigs.get(0);
        }
        else if (candidateCount > 1) {
            ILaunchConfiguration choosen = LaunchUIUtil.chooseConfiguration(candidateConfigs, "Symbolic Execution Debugger (SED)");
            if (choosen == null) {
                throw new OperationCanceledException();
            }
            return choosen;
        }
        else {
            return null;
        }
    }
    
    /**
     * Launches the given {@link IMethod}.
     * @param method The {@link IMethod} to launch.
     * @param mode The mode to use.
     * @param methodStartPosition An optional start position to execute only parts of the method.
     * @param methodEndPosition An optional end position to execute only parts of the method.
     * @throws CoreException Occurred Exception.
     */
    public static void launch(IMethod method, 
                              String mode,
                              Position methodStartPosition,
                              Position methodEndPosition) throws CoreException {
        try {
            ILaunchConfiguration config = findLaunchConfiguration(method, methodStartPosition, methodEndPosition);
            if (config == null) {
                config = KeySEDUtil.createConfiguration(method, methodStartPosition, methodEndPosition);
            }
            if (config != null) {
                DebugUITools.launch(config, mode);
            }
        }
        catch (OperationCanceledException e) {
            // Nothing to do
        }
    }
    
    /**
     * Tries to find an existing {@link ILaunchConfiguration} for the
     * given {@link IMethod}. If multiple {@link ILaunchConfiguration} exists
     * the user is asked to select one.
     * @param method The {@link IMethod} for that an {@link ILaunchConfiguration} is needed.
     * @param methodStartPosition An optional start position to execute only parts of the method.
     * @param methodEndPosition An optional end position to execute only parts of the method.
     * @return The found {@link ILaunchConfiguration} or {@code null} if no one was found.
     * @throws CoreException Occurred Exception.
     * @throws OperationCanceledException When the user has canceled the select dialog.
     */
    public static ILaunchConfiguration findLaunchConfiguration(IMethod method,
                                                               Position methodStartPosition,
                                                               Position methodEndPosition) throws CoreException {
        List<ILaunchConfiguration> candidateConfigs = KeySEDUtil.searchLaunchConfigurations(method, methodStartPosition, methodEndPosition);
        int candidateCount = candidateConfigs.size();
        if (candidateCount == 1) {
            return (ILaunchConfiguration)candidateConfigs.get(0);
        }
        else if (candidateCount > 1) {
            ILaunchConfiguration choosen = LaunchUIUtil.chooseConfiguration(candidateConfigs, "Symbolic Execution Debugger (SED)");
            if (choosen == null) {
                throw new OperationCanceledException();
            }
            return choosen;
        }
        else {
            return null;
        }
    }
}