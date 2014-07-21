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

package de.hentschel.visualdbc.datasource.model;

import java.util.List;

import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Defines something that is provable via a proof.
 * @author Martin Hentschel
 */
public interface IDSProvable {
   /**
    * Returns all possible obligations.
    * @return All possible obligations.
    * @throws DSException Occurred Exception
    */
   public List<String> getObligations() throws DSException;
   
   /**
    * Checks if the given obligation is valid.
    * @param obligation The obligation to check.
    * @return {@code true} is valid, {@code false} is not valid.
    * @throws DSException Occurred Exception
    */
   public boolean isValidObligation(String obligation) throws DSException;
   
   /**
    * Opens the interactive proof UI to fulfill the obligation.
    * @param obligation The obligation to fulfill by the user.
    * @throws DSException Occurred Exception.
    * @throws DSCanceledException If the progress was canceled.
    * @return The opened {@link IDSProof}.
    */
   public IDSProof openInteractiveProof(String obligation) throws DSException, DSCanceledException;
   
   /**
    * Returns the opened proof for the given obligation.
    * @param obligation The obligation for that the opened proof is needed.
    * @return The opened proof or {@code null} if currently no proof is opened.
    * @throws DSException Occurred Exception.
    */
   public IDSProof getInteractiveProof(String obligation) throws DSException;
   
   /**
    * Checks if a still running and existing proof is opened for the given obligation.
    * @param obligation The obligation to check.
    * @return {@code true} = has running valid proof, {@code false} = proof not opened or no longer valid.
    * @throws DSException Occurred Exception.
    */
   public boolean hasInteractiveProof(String obligation) throws DSException;
}