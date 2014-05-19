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

package de.hentschel.visualdbc.datasource.key.intern.helper;

import org.eclipse.core.runtime.Assert;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * This class contains the {@link ProofOblInput} and the opened {@link Proof}.
 * The class allows also to read all references that are defined by the 
 * {@link ProofOblInput}.
 * @author Martin Hentschel
 */
public class OpenedProof {
   /**
    * The {@link ProofOblInput}.
    */
   private ProofOblInput input;
   
   /**
    * The {@link Proof}.
    */
   private Proof proof;

   /**
    * Constructor.
    * @param input The {@link ProofOblInput}.
    * @param assumedInvs The assumed invariants or {@code null} if no one exist.
    * @param ensuredInvs The ensured invariants or {@code null} if no one exist.
    */
   public OpenedProof(ProofOblInput input) {
      Assert.isNotNull(input);
      this.input = input;
   }

   /**
    * Returns the {@link ProofOblInput}.
    * @return The {@link ProofOblInput}.
    */
   public ProofOblInput getInput() {
      return input;
   }

   /**
    * Returns the {@link Proof}.
    * @return The {@link Proof}.
    */
   public Proof getProof() {
      return proof;
   }

   /**
    * Sets the {@link Proof}.
    * @param proof The {@link Proof} to set.
    */
   public void setProof(Proof proof) {
      this.proof = proof;
   }
}