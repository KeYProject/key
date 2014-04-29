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