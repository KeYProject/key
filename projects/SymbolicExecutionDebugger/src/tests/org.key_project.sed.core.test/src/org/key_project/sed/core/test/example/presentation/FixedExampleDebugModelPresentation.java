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

package org.key_project.sed.core.test.example.presentation;

import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.ui.IEditorInput;
import org.key_project.sed.ui.presentation.AbstractSEDDebugModelPresentation;

/**
 * {@link IDebugModelPresentation} for the fixed example.
 * @author Martin Hentschel
 */
public class FixedExampleDebugModelPresentation extends AbstractSEDDebugModelPresentation implements IDebugModelPresentation {
   /**
    * {@inheritDoc}
    */
   @Override
   public IEditorInput getEditorInput(Object element) {
      return null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getEditorId(IEditorInput input, Object element) {
      return null;
   }
}