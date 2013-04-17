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

import java.util.List;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
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
    * Checks if this {@link IRuleAnalyst} implementation can handle the 
    * given {@link Node} in the proof tree.
    * @param connection The {@link KeyConnection} that has opened KeY.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} to handle.
    * @return {@code true} can handle given {@link Node}, {@code false} can't handle given {@link Node}.
    */
   public boolean canHandle(KeyConnection connection,
                            Services services, 
                            Node node);
   
   /**
    * This method is called if {@link #canHandle(KeyConnection, Services, Node)} 
    * is {@code true} to extract the contained references in the given {@link Node}.
    * @param connection The {@link KeyConnection} that has opened KeY.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} to handle.
    * @return A {@link List} with the found references as instances of {@link IDSProvableReference}.
    */
   public List<IDSProvableReference> getReferences(KeyConnection connection,
                                                   Services services, 
                                                   Node node);
}