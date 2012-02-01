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
