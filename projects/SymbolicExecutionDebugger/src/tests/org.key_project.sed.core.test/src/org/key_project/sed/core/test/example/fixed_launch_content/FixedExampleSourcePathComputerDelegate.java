package org.key_project.sed.core.test.example.fixed_launch_content;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.sourcelookup.ISourceContainer;
import org.eclipse.debug.core.sourcelookup.ISourcePathComputerDelegate;
import org.eclipse.debug.core.sourcelookup.containers.WorkspaceSourceContainer;

/**
 * {@link ISourcePathComputerDelegate} for the fixed example.
 * It returns just the whole workspace.
 * @author Martin Hentschel
 */
public class FixedExampleSourcePathComputerDelegate implements ISourcePathComputerDelegate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ISourceContainer[] computeSourceContainers(ILaunchConfiguration configuration, IProgressMonitor monitor) throws CoreException {
        return new ISourceContainer[] {new WorkspaceSourceContainer()};
    }
}
