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

package de.hentschel.visualdbc.statistic.ui.command;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IViewActionDelegate;
import org.eclipse.ui.IViewPart;

import de.hentschel.visualdbc.statistic.ui.view.StatisticViewPart;

/**
 * Opens the dialog to select the proof obligations to show.
 * @author Martin Hentschel
 */
public class SelectProofObligationsViewActionDelegate implements IViewActionDelegate {
   /**
    * The {@link IViewPart} that contains the action.
    */
   private IViewPart viewPart;

   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IAction action) {
      if (viewPart instanceof StatisticViewPart) {
         ((StatisticViewPart)viewPart).openSelectProofObligationsDialog();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void selectionChanged(IAction action, ISelection selection) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewPart view) {
      this.viewPart = view;
   }
}