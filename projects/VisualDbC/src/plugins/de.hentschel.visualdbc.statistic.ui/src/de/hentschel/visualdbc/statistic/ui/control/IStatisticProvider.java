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

package de.hentschel.visualdbc.statistic.ui.control;

import org.eclipse.jface.viewers.ISelection;

import de.hentschel.visualdbc.dbcmodel.DbcModel;

/**
 * Defines the methods that are required to show content 
 * in a {@link StatisticComposite}.
 * @author Martin Hentschel
 */
public interface IStatisticProvider {
   /**
    * Returns the {@link DbcModel}.
    * @return The {@link DbcModel}.
    */
   public DbcModel getModel();
   
   /**
    * Selects the given elements in the provider.
    * @param selection The elements to select.
    */
   public void select(ISelection selection);
}