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

import java.util.List;

/**
 * Defines the methods that are required to show content 
 * in a {@link ProofReferenceComposite}.
 * @author Martin Hentschel
 */
public interface IProofReferenceProvider {
   /**
    * Extracts the elements to show from the given one.
    * @param elements The given elements.
    * @return The elements to show.
    */
   public List<?> extractElementsToShow(List<?> elements);

   /**
    * Selects the given elements in the provider.
    * @param toSelect The elements to select.
    */
   public void select(List<?> toSelect);
}