package org.key_project.sed.ui.visualization.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.sourcelookup.ISourceContainer;
import org.eclipse.debug.core.sourcelookup.ISourceContainerTypeDelegate;
import org.eclipse.debug.core.sourcelookup.containers.AbstractSourceContainerTypeDelegate;

/**
 * Implementation of {@link ISourceContainerTypeDelegate} which uses a
 * {@link AbsoluteFileSystemPathSourceContainer}.
 * @author Martin Hentschel
 */
public class AbsoluteFileSystemPathSourceContainerTypeDelegate extends AbstractSourceContainerTypeDelegate {
   /**
    * {@inheritDoc}
    */
   @Override
   public ISourceContainer createSourceContainer(String memento) throws CoreException {
      return AbsoluteFileSystemPathSourceContainer.INSTANCE;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getMemento(ISourceContainer container) throws CoreException {
      return null;
   }
}
