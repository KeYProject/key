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

package org.key_project.keyide.ui.editor.input;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.ui.IEditorInput;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * This {@link IEditorInput} is used to open an existing {@link Proof}.
 * @author Martin Hentschel
 */
public class ProofEditorInput extends AbstractProofEditorInput {
   /**
    * The {@link Proof}.
    */
   private Proof proof;

   /**
    * {@code true} can start auto mode, {@code false} is not allowed to start auto mode.
    */
   private boolean canStartAutomode;

   /**
    * {@code true} can apply rules, {@code false} is not allowed to apply rules.
    */
   private boolean canApplyRules;

   /**
    * {@code true} can prune proof, {@code false} is not allowed to prune proof.
    */
   private boolean canPruneProof;

   /**
    * {@code true} can start SMT solver, {@code false} is not allowed to start SMT solver.
    */
   private boolean canStartSMTSolver;
   
   /**
    * Constructor.
    * @param proof The {@link Proof}.
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    * @param method An optional {@link IMethod} from which the {@link Proof} was started.
    * @param canStartAutomode {@code true} can start auto mode, {@code false} is not allowed to start auto mode.
    * @param canApplyRules {@code true} can apply rules, {@code false} is not allowed to apply rules.
    * @param canPruneProof {@code true} can prune proof, {@code false} is not allowed to prune proof.
    * @param canStartSMTSolver {@code true} can start SMT solver, {@code false} is not allowed to start SMT solver.
    */
   public ProofEditorInput(Proof proof, 
                           KeYEnvironment<CustomConsoleUserInterface> environment, 
                           IMethod method,
                           boolean canStartAutomode,
                           boolean canApplyRules,
                           boolean canPruneProof,
                           boolean canStartSMTSolver) {
      super(environment, method, proof.name().toString());
      Assert.isNotNull(proof);
      this.proof = proof;
      this.canStartAutomode = canStartAutomode;
      this.canApplyRules = canApplyRules;
      this.canPruneProof = canPruneProof;
      this.canStartSMTSolver = canStartSMTSolver;
   }
   
   /**
    * Returns the {@link Proof}.
    * @return The {@link Proof}.
    */
   public Proof getProof() {
      return proof;
   }

   /**
    * Checks if it is allowed to start the auto mode.
    * @return {@code true} can start auto mode, {@code false} is not allowed to start auto mode.
    */
   public boolean isCanStartAutomode() {
      return canStartAutomode;
   }

   /**
    * Checks if it is allowed to apply rules.
    * @return {@code true} can apply rules, {@code false} is not allowed to apply rules.
    */
   public boolean isCanApplyRules() {
      return canApplyRules;
   }

   /**
    * Checks if it is allowed to prune proof.
    * @return {@code true} can prune proof, {@code false} is not allowed to prune proof.
    */
   public boolean isCanPruneProof() {
      return canPruneProof;
   }

   /**
    * Checks if it is allowed to start SMT solver.
    * @return {@code true} can start SMT solver, {@code false} is not allowed to start SMT solver.
    */
   public boolean isCanStartSMTSolver() {
      return canStartSMTSolver;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int hashCode() {
      return ObjectUtil.hashCode(getProof());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof ProofEditorInput) {
         return ObjectUtil.equals(getProof(), ((ProofEditorInput)obj).getProof());
      }
      else {
         return false;
      }
   }
}