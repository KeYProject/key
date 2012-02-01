package org.key_project.sed.key.core.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.eclipse.jdt.core.IMethod;
import org.key_project.sed.key.core.util.KeySEDUtil;

/**
 * This {@link LaunchConfigurationDelegate} is responsible to start
 * the Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYLaunchConfigurationDelegate extends LaunchConfigurationDelegate {
    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(ILaunchConfiguration configuration, 
                       String mode, 
                       ILaunch launch, 
                       IProgressMonitor monitor) throws CoreException {
        IMethod method = KeySEDUtil.findMethod(launch);
        System.out.println("Debugging: " + method);
    }
}
