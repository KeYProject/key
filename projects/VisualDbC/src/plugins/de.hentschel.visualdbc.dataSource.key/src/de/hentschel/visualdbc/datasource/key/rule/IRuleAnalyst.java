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

package de.hentschel.visualdbc.datasource.key.rule;

import java.util.LinkedHashSet;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

/**
 * Implementations of this interface are used in {@link KeyProofReferenceUtil}
 * to extract the references of a given {@link Node}.
 * @author Martin Hentschel
 * @see KeyProofReferenceUtil
 */
public interface IRuleAnalyst {
   /**
    * This method is called to extract the contained references in the given {@link Node}.
    * @param connection The {@link KeyConnection} that has opened KeY.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} to handle.
    * @return An {@link ImmutableList} with the found references as instances of {@link IDSProvableReference}.
    * @throws DSException Occurred Exception
    */
   public LinkedHashSet<IDSProvableReference> getReferences(KeyConnection connection,
                                                            Services services, 
                                                            Node node) throws DSException;
}