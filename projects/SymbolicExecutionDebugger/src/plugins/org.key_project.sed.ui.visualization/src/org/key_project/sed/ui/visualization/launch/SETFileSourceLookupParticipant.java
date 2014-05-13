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
import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupParticipant;
import org.key_project.sed.core.model.ISourcePathProvider;

/**
 * {@link AbstractSourceLookupParticipant} implementation for the
 * Symbolic Execution Debugger based on SET files.
 * @author Martin Hentschel
 */
public class SETFileSourceLookupParticipant extends AbstractSourceLookupParticipant {
   /**
    * {@inheritDoc}
    */
   public String getSourceName(Object object) throws CoreException {
      if (object instanceof ISourcePathProvider) {
         return ((ISourcePathProvider) object).getSourcePath();
      }
      else {
         return null;
      }
   }
}