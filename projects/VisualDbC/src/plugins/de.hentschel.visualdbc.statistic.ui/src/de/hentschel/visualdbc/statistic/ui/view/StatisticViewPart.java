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

package de.hentschel.visualdbc.statistic.ui.view;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorPart;

/**
 * This view shows the statistics for the active editor. To enable the
 * statistics the {@link IAdaptable#getAdapter(Class)} method of the editor
 * must return an {@link IStatisticViewPart} instance.
 * @author Martin Hentschel
 */
public class StatisticViewPart extends AbstractEditorBasedViewPart {
   /**
    * Maps the {@link Control} back to the {@link IStatisticViewPart} that has created it.
    */
   private Map<Control, IStatisticViewPart> controlViewPartMapping = new HashMap<Control, IStatisticViewPart>();
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createControlFor(IEditorPart activeEditor, Composite parent) {
      Object statisticPart = activeEditor.getAdapter(IStatisticViewPart.class);
      if (statisticPart instanceof IStatisticViewPart) {
         Control control = ((IStatisticViewPart)statisticPart).createControl(parent);
         controlViewPartMapping.put(control, (IStatisticViewPart)statisticPart);
         return control;
      }
      else {
         return null;
      }
   }
   
   /**
    * Opens the dialog to select proof obligations.
    */
   public void openSelectProofObligationsDialog() {
      Control activeControl = getActiveControl();
      if (activeControl != null) {
         IStatisticViewPart statisticPart = controlViewPartMapping.get(activeControl);
         if (statisticPart != null) {
            statisticPart.openSelectProofObligationsDialog();
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      controlViewPartMapping.clear();
      super.dispose();
   }
}