/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.model;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.key.intern.helper.OpenedProof;
import de.hentschel.visualdbc.datasource.key.rule.KeyProofReferenceUtil;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProof;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Special KeY implementation of {@link IDSProof}.
 * @author Martin Hentschel
 */
public class KeyProof extends MemoryProof {
   /**
    * The opened proof instance or {@code null} if no proof is opened.
    */
   private Proof proof;
   
   /**
    * The {@link KeyConnection} that has created this instance.
    */
   private KeyConnection connection;

   /**
    * Contains the {@link IDSProvableReference} that are defined by {@link ProofOblInput}.
    */
   private List<IDSProvableReference> inputReferences = null;
   
   /**
    * Constructor
    * @param proof The KeY proof to represent.
    * @param connection The {@link KeyConnection} that has created this instance.
    * @throws DSException Occurred Exception
    */
   public KeyProof(OpenedProof proofResult,
                   KeyConnection connection) throws DSException {
      super();
      Assert.isNotNull(proofResult);
      Assert.isNotNull(proofResult.getProof());
      Assert.isNotNull(connection);
      this.proof = proofResult.getProof();
      this.connection = connection;
      proof.addProofTreeListener(new ProofTreeAdapter() {
         @Override
         public void proofClosed(ProofTreeEvent e) {
            handleProofClosed(e);
         }

         @Override
         public void proofStructureChanged(ProofTreeEvent e) {
            handleProofStructureChanged(e);
         }

         @Override
         public void proofExpanded(ProofTreeEvent e) {
            handleProofExpanded(e);
         }

         @Override
         public void proofPruned(ProofTreeEvent e) {
            handleProofPruned(e);
         }
      });
      analyzeProofInput(proofResult);
   }

   /**
    * Analyzes the initial proof references that are defined via
    * {@link OpenedProof} and his contained {@link ProofOblInput}.
    * @param result The {@link OpenedProof} to analyze.
    * @throws DSException Occurred Exception
    */
   protected void analyzeProofInput(OpenedProof result) throws DSException {
      inputReferences = new LinkedList<IDSProvableReference>();
      // Update the proof references.
      setReferences(inputReferences);
   }

   /**
    * Handles the event {@link ProofTreeListener#proofClosed(ProofTreeEvent)}.
    * @param e The event to handle.
    */
   protected void handleProofClosed(ProofTreeEvent e) {
      setClosed(true);
      fireProofClosed(new DSProofEvent(this));
   }

   /**
    * Handles the event {@link ProofTreeListener#proofExpanded(ProofTreeEvent)}.
    * @param e The event to handle.
    */
   protected void handleProofExpanded(ProofTreeEvent e) {
      updateReferences();
   }

   /**
    * Handles the event {@link ProofTreeListener#proofPruned(ProofTreeEvent)}.
    * @param e The event to handle.
    */
   protected void handleProofPruned(ProofTreeEvent e) {
      updateReferences();
   }

   /**
    * Handles the event {@link ProofTreeListener#proofStructureChanged(ProofTreeEvent)}.
    * @param e The event to handle.
    */
   protected void handleProofStructureChanged(ProofTreeEvent e) {
      updateReferences();
   }
   
   /**
    * Updates all available references by reanalyzing the complete proof tree.
    */
   // TODO: Implement test for pruned proof trees
   protected void updateReferences() {
      // Get required parameters
      Services services = connection.getServices();
      // Analyze tree
      List<IDSProvableReference> references = KeyProofReferenceUtil.analyzeProof(connection, services, proof);
      // Add initial references from the ProofObjInput.
      if (inputReferences != null) {
         references.addAll(inputReferences);
      }
      // Update the available references.
      setReferences(references);
   }
   
   /**
    * Sets the new available proof references and fires the events.
    * @param references The new references to set.
    */
   protected void setReferences(List<IDSProvableReference> references) {
      synchronized (getProofReferences()) {
         // Check if the references have changed
         if (!getProofReferences().equals(references)) {
            // Get the old references
            List<IDSProvableReference> oldReferences = new LinkedList<IDSProvableReference>(getProofReferences());
            // Remove all old references
            getProofReferences().clear();
            // Add new references
            getProofReferences().addAll(references);
            // Inform listeners about the new references
            fireReferencesChanged(new DSProofEvent(this, oldReferences, references));
         }
      }
   }

   /**
    * Returns the represented key proof.
    * @return The key proof.
    */
   public Proof getProof() {
      return proof;
   }
}
