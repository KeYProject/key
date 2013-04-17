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

package org.key_project.sed.ui.util;

import java.util.List;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Provides static methods for the UI functionality of the Eclipse Debugger API.
 * @author Martin Hentschel
 */
public final class LaunchUIUtil {
    /**
     * Forbid instances.
     */
    private LaunchUIUtil() {
    }
    
    /**
     * Opens a dialog to select one of the given {@link ILaunchConfiguration}s.
     * @param configurations The available {@link ILaunchConfiguration}s.
     * @param title The dialog title.
     * @return The selected {@link ILaunchConfiguration} or {@code null} if the user cancelled the Dialog.
     */
    public static ILaunchConfiguration chooseConfiguration(List<ILaunchConfiguration> configurations,
                                                           String title) {
        IDebugModelPresentation labelProvider = null;
        try {
            labelProvider = DebugUITools.newDebugModelPresentation();
            ElementListSelectionDialog dialog = new ElementListSelectionDialog(WorkbenchUtil.getActiveShell(), 
                                                                               labelProvider);
            dialog.setElements(configurations.toArray());
            dialog.setTitle(title);  
            dialog.setMessage("&Select existing configuration:");
            dialog.setMultipleSelection(false);
            if (dialog.open() == ElementListSelectionDialog.OK) {
                return (ILaunchConfiguration) dialog.getFirstResult();
            }
            else {
                return null;
            }
        }
        finally {
            if (labelProvider != null) {
                labelProvider.dispose();
            }
        }
    }
}