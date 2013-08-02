/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.key.ui.presentation;

import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.jdt.internal.debug.ui.JDIModelPresentation;
import org.eclipse.ui.IEditorInput;
import org.key_project.sed.ui.presentation.AbstractSEDDebugModelPresentation;

/**
 * {@link IDebugModelPresentation} for the Symbolic Execution Debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYDebugModelPresentation extends AbstractSEDDebugModelPresentation implements IDebugModelPresentation {
   /**
    * Helper {@link IDebugModelPresentation} from Java Debug API.
    */
   private JDIModelPresentation helper = new JDIModelPresentation();
   
   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Copied from {@link JDIModelPresentation#getEditorInput(Object)}.
    * </p>
    */
   @Override
   public IEditorInput getEditorInput(Object element) {
      return helper.getEditorInput(element);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getEditorId(IEditorInput input, Object element) {
      return helper.getEditorId(input, element);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      super.dispose();
      helper.dispose();
   }
}