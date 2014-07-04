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

package org.key_project.util.test.editor;

import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;

/**
 * {@link IEditorActionBarContributor} for {@link TextControlEditor} instances.
 * @author Martin Hentschel
 */
public class TextControlEditorContributor implements IEditorActionBarContributor, IGlobalEnablement {
   /**
    * The global enabled.
    */
   private boolean globalEnabled;

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IActionBars bars, IWorkbenchPage page) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setActiveEditor(IEditorPart targetEditor) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGlobalEnabled() {
      return globalEnabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setGlobalEnabled(boolean globalEnabled) {
      this.globalEnabled = globalEnabled;
   }
}