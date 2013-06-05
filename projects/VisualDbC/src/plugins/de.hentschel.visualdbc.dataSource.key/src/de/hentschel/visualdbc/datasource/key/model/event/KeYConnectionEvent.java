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

package de.hentschel.visualdbc.datasource.key.model.event;

import java.util.EventObject;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyProof;

/**
 * An event thrown from a {@link KeyConnection}.
 * @author Martin Hentschel
 */
public class KeYConnectionEvent extends EventObject {
   /**
    * Generated UID. 
    */
   private static final long serialVersionUID = 8617858896279729196L;

   /**
    * The {@link KeyProof}.
    */
   private KeyProof proof;
   
   /**
    * Constructor.
    * @param source The {@link KeyConnection}.
    * @param proof The {@link KeyProof}.
    */
   public KeYConnectionEvent(KeyConnection source, KeyProof proof) {
      super(source);
      this.proof = proof;
   }

   /**
    * Returns the {@link KeyProof}.
    * @return The {@link KeyProof}.
    */
   public KeyProof getProof() {
      return proof;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeyConnection getSource() {
      return (KeyConnection)super.getSource();
   }
}