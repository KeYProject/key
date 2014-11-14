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

package de.hentschel.visualdbc.datasource.key.model;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.key.intern.helper.OpenedProof;
import de.hentschel.visualdbc.datasource.key.rule.KeyProofReferenceUtil;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProof;
import de.uka.ilkd.key.core.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Special KeY implementation of {@link IDSProof}.
 * @author Martin Hentschel
 */
public class KeyProof extends MemoryProof implements IDisposable {
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
    * Indicates that the auto mode is active or not.
    */
   private boolean autoModeActive = false;
   
   /**
    * Listens for changes on {@link #proof}.
    */
   private ProofTreeListener proofTreeListener = new ProofTreeAdapter() {
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
   };
   
   /**
    * Listens for auto mode changes on the {@link KeYMediator} of
    * {@link MainWindow#getInstance()}.
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         handleAutoModeStopped(e);
      }
      
      @Override
      public void autoModeStarted(ProofEvent e) {
         handleAutoModeStarted(e);
      }
   };
   
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
      this.connection.registerProof(this); // Register KeyProof in KeyConnection to make sure that it is disposed during disconnect.
      proof.addProofTreeListener(proofTreeListener);
      MainWindow.getInstance().getMediator().addAutoModeListener(autoModeListener);
      analyzeProofInput(proofResult);
   }

   /**
    * When the auto mode was started.
    * @param e The event.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      if (ObjectUtil.equals(proof, e.getSource())) {
         autoModeActive = true;
      }
   }

   
   /**
    * When the auto mode was stopped.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      if (ObjectUtil.equals(proof, e.getSource())) {
         autoModeActive = false;
         updateReferences();
      }
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
      if (e.getNode() != null) { // Update references only if a rule was applied.
         updateReferences();
      }
   }

   /**
    * Handles the event {@link ProofTreeListener#proofPruned(ProofTreeEvent)}.
    * @param e The event to handle.
    */
   protected void handleProofPruned(ProofTreeEvent e) {
      if (e.getNode() != null) { // Update references only if a rule was applied.
         updateReferences();
      }
   }

   /**
    * Handles the event {@link ProofTreeListener#proofStructureChanged(ProofTreeEvent)}.
    * @param e The event to handle.
    */
   protected void handleProofStructureChanged(ProofTreeEvent e) {
      if (e.getNode() != null) { // Update references only if a rule was applied.
         updateReferences();
      }
   }
   
   /**
    * Updates all available references by reanalyzing the complete proof tree.
    */
   // TODO: Implement test for pruned proof trees
   protected void updateReferences() {
      if (!autoModeActive) {
         // Get required parameters
         Services services = connection.getServices();
         // Analyze tree
         List<IDSProvableReference> references = new LinkedList<IDSProvableReference>(); 
         references.addAll(KeyProofReferenceUtil.analyzeProof(connection, services, proof));
         // Add initial references from the ProofObjInput.
         if (inputReferences != null) {
            references.addAll(inputReferences);
         }
         // Update the available references.
         setReferences(references);
      }
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

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      proof.removeProofTreeListener(proofTreeListener);
      MainWindow.getInstance().getMediator().removeAutoModeListener(autoModeListener);
      MainWindow.getInstance().getUserInterface().removeProof(proof);
   }
}