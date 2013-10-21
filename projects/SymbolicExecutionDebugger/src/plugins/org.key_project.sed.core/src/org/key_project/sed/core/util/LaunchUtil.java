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

package org.key_project.sed.core.util;

import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;


/**
 * Provides static utility methods for the Eclipse Debug Launch functionality.
 * @author Martin Hentschel
 */
public final class LaunchUtil {
    /**
     * Forbid instances.
     */
    private LaunchUtil() {
    }
    
    public static ILaunchManager getLaunchManager() {
        return DebugPlugin.getDefault().getLaunchManager();
    }
    
    public static ILaunchConfigurationType getConfigurationType(String launchConfigurationTypeId) {
        return getLaunchManager().getLaunchConfigurationType(launchConfigurationTypeId);            
    }
}