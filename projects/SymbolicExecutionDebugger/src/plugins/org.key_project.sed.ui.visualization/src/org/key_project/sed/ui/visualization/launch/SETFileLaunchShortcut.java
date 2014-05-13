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

package org.key_project.sed.ui.visualization.launch;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.ILaunchShortcut;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorPart;
import org.key_project.sed.ui.util.LaunchUIUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.sed.ui.visualization.util.SETFileLaunchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ILaunchShortcut} implementation for Symbolic Executiong Debugger
 * based on SET files.
 * @author Martin Hentschel
 */
public class SETFileLaunchShortcut implements ILaunchShortcut {
    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(ISelection selection, String mode) {
       try {
          Object[] elements = SWTUtil.toArray(selection);
          for (Object element : elements) {
             if (element instanceof IFile) {
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
    }
    
    /**
     * Launches the given {@link IFile}.
     * @param file The {@link IFile} to launch.
     * @param mode The mode to use.
     * @throws CoreException Occurred Exception.
     */
    protected void launch(IFile file, 
                          String mode) throws CoreException {
        try {
            ILaunchConfiguration config = findLaunchConfiguration(file);
            if (config == null) {
                config = SETFileLaunchUtil.createConfiguration(file);
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
    protected ILaunchConfiguration findLaunchConfiguration(IFile file) throws CoreException {
        List<ILaunchConfiguration> candidateConfigs = SETFileLaunchUtil.searchLaunchConfigurations(file);
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