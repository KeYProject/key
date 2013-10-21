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

package de.hentschel.visualdbc.statistic.ui.view;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorPart;

/**
 * This view shows the proof references of the selected elements in the active 
 * editor. To enable the proof references the {@link IAdaptable#getAdapter(Class)} 
 * method of the editor must return an {@link IProofReferencesViewPart} instance.
 * @author Martin Hentschel
 */
public class ProofReferencesViewPart extends AbstractEditorBasedViewPart {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createControlFor(IEditorPart activeEditor, Composite parent) {
      Object statisticPart = activeEditor.getAdapter(IProofReferencesViewPart.class);
      if (statisticPart instanceof IProofReferencesViewPart) {
         return ((IProofReferencesViewPart)statisticPart).createControl(parent);
      }
      else {
         return null;
      }
   }
}