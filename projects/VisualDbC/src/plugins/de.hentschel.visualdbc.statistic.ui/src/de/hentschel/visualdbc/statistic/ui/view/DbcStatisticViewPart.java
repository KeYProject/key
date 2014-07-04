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

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.statistic.ui.control.IStatisticProvider;
import de.hentschel.visualdbc.statistic.ui.control.StatisticComposite;

/**
 * Implementation of {@link IStatisticViewPart} to show statiscs of
 * {@link DbcModel}s.
 * @author Martin Hentschel
 */
public class DbcStatisticViewPart implements IStatisticViewPart {
   /**
    * The used {@link IStatisticProvider}.
    */
   private IStatisticProvider statisticProvider;
   
   /**
    * The created and manged {@link StatisticComposite}.
    */
   private StatisticComposite statisticComposite;

   /**
    * Constructor.
    * @param statisticProvider The {@link IStatisticProvider} to use.
    */
   public DbcStatisticViewPart(IStatisticProvider statisticProvider) {
      super();
      Assert.isNotNull(statisticProvider);
      this.statisticProvider = statisticProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Control createControl(Composite parent) {
      statisticComposite = new StatisticComposite(parent, SWT.NONE, statisticProvider);
      return statisticComposite;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void openSelectProofObligationsDialog() {
      if (statisticComposite != null) {
         statisticComposite.openSelectProofObligationsDialog();
      }
   }
}