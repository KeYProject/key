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

package org.key_project.sed.example.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupParticipant;
import org.eclipse.debug.core.sourcelookup.ISourceContainer;
import org.eclipse.debug.core.sourcelookup.ISourcePathComputerDelegate;
import org.eclipse.debug.core.sourcelookup.containers.WorkspaceSourceContainer;

/**
 * An {@link ISourcePathComputerDelegate} provides the {@link ISourceContainer}
 * in which source files of paths computed by an 
 * {@link AbstractSourceLookupParticipant} are searched in.
 * <p>
 * Even if the {@link ExampleSourceLookupParticipant} will not provide any paths
 * the {@link WorkspaceSourceContainer} is provided.
 * @author Martin Hentschel
 */
public class ExampleSourcePathComputerDelegate implements ISourcePathComputerDelegate {
   /**
    * {@inheritDoc}
    */
   @Override
   public ISourceContainer[] computeSourceContainers(ILaunchConfiguration configuration, IProgressMonitor monitor) throws CoreException {
      return new ISourceContainer[] {new WorkspaceSourceContainer()};
   }
}