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

package de.hentschel.visualdbc.statistic.ui.adapter;

import org.eclipse.core.runtime.IAdapterFactory;

import de.hentschel.visualdbc.statistic.ui.view.IStatisticViewPart;

/**
 * Provides a basic implementation for {@link IAdapterFactory}s that
 * allows to convert to {@link IStatisticViewPart}.
 * @author Martin Hentschel
 */
public abstract class AbstractStatisticAdapterFactory implements IAdapterFactory {
   @SuppressWarnings("rawtypes")
   @Override
   public Class[] getAdapterList() {
      return new Class[] {IStatisticViewPart.class};
   }
}