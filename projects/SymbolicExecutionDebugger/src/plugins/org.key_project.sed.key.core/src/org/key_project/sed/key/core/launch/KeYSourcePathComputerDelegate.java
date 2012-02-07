package org.key_project.sed.key.core.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.sourcelookup.ISourceContainer;
import org.eclipse.debug.core.sourcelookup.ISourcePathComputerDelegate;
import org.eclipse.debug.core.sourcelookup.containers.WorkspaceSourceContainer;

/**
 * {@link ISourcePathComputerDelegate} for the Symbolic Execution Debugger
 * based on KeY. It returns just the whole workspace.
 * @author Martin Hentschel
 */
public class KeYSourcePathComputerDelegate implements ISourcePathComputerDelegate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ISourceContainer[] computeSourceContainers(ILaunchConfiguration configuration, IProgressMonitor monitor) throws CoreException {
        return new ISourceContainer[] {new WorkspaceSourceContainer()};
    }
}
