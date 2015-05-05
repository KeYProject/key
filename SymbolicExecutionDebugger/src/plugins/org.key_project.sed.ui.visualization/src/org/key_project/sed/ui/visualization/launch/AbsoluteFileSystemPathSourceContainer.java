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

import java.io.File;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.sourcelookup.ISourceContainer;
import org.eclipse.debug.core.sourcelookup.ISourceContainerType;
import org.eclipse.debug.core.sourcelookup.containers.AbstractSourceContainer;
import org.eclipse.debug.core.sourcelookup.containers.LocalFileStorage;

/**
 * An {@link ISourceContainer} which uses a file in the file system
 * assuming that the full path is given.
 * @author Martin Hentschel
 */
public final class AbsoluteFileSystemPathSourceContainer extends AbstractSourceContainer {
   /**
    * The only instance of this class.
    */
   public static final AbsoluteFileSystemPathSourceContainer INSTANCE = new AbsoluteFileSystemPathSourceContainer(); 

   /**
    * Forbid instances.
    */
   private AbsoluteFileSystemPathSourceContainer() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Object[] findSourceElements(String name) throws CoreException {
      if (name != null) {
         File file = new File(name);
         if (file.exists()) {
            return new LocalFileStorage[] {new LocalFileStorage(new File(name))};
         }
         else {
            return EMPTY;
         }
      }
      else {
         return EMPTY;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Absolute File System Paths";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISourceContainerType getType() {
      return getSourceContainerType("org.key_project.sed.ui.visualization.absoluteFileSystemPathsSourceContainerType");
   }
}