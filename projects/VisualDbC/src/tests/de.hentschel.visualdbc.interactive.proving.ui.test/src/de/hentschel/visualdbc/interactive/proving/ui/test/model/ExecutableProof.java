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

package de.hentschel.visualdbc.interactive.proving.ui.test.model;

import java.util.LinkedList;
import java.util.List;

import org.key_project.util.java.CollectionUtil;

import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProof;

/**
 * Implementation of {@link IDSProof} where throwing events is possible
 * for test purpose.
 * @author Martin Hentschel
 */
public class ExecutableProof extends MemoryProof {
   /**
    * Closes the proof and fires the event.
    */
   public void closeProof() {
      fireProofClosed(new DSProofEvent(this));
   }

   /**
    * Adds the references and fires the change event.
    * @param referencesToAdd The references to add.
    */
   public void addReferences(IDSProvableReference... referencesToAdd) {
      synchronized (getProofReferences()) {
         List<IDSProvableReference> oldReferences = new LinkedList<IDSProvableReference>(getProofReferences());
         CollectionUtil.addAll(getProofReferences(), referencesToAdd);
         fireReferencesChanged(new DSProofEvent(this, oldReferences, getProofReferences()));
      }
   }

   /**
    * Removes the references and fires the change event.
    * @param referencesToRemove The references to add.
    */
   public void removeReferences(IDSProvableReference... referencesToRemove) {
      synchronized (getProofReferences()) {
         List<IDSProvableReference> oldReferences = new LinkedList<IDSProvableReference>(getProofReferences());
         CollectionUtil.removeAll(getProofReferences(), referencesToRemove);
         fireReferencesChanged(new DSProofEvent(this, oldReferences, getProofReferences()));
      }
   }
}