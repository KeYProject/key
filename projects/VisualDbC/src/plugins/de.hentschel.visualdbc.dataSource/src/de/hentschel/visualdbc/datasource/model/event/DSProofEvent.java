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

package de.hentschel.visualdbc.datasource.model.event;

import java.util.EventObject;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;

/**
 * An event thrown from an {@link IDSProof}.
 * @author Martin Hentschel
 */
public class DSProofEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -6728950695500147051L;

   /**
    * The old references.
    */
   private List<IDSProvableReference> oldReferences;

   /**
    * The new references.
    */
   private List<IDSProvableReference> newReferences;
   
   /**
    * Constructor.
    * @param source The source {@link IDSProof} that has thrown this event.
    */
   public DSProofEvent(IDSProof source) {
      super(source);
   }

   /**
    * Constructor.
    * @param source The source {@link IDSProof} that has thrown this event.
    * @param oldReferences The old references.
    * @param newReferences The new references.
    */
   public DSProofEvent(IDSProof source, 
                       List<IDSProvableReference> oldReferences, 
                       List<IDSProvableReference> newReferences) {
      super(source);
      this.oldReferences = oldReferences;
      this.newReferences = newReferences;
   }
   
   /**
    * Returns the old references.
    * @return The old references.
    */
   public List<IDSProvableReference> getOldReferences() {
      return oldReferences;
   }
   
   /**
    * Returns the new references.
    * @return The new references.
    */
   public List<IDSProvableReference> getNewReferences() {
      return newReferences;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProof getSource() {
      return (IDSProof)super.getSource();
   }
}