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

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * This class is used to define an input to display in the editor
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofOblInputEditorInput extends AbstractProofEditorInput {
   /**
    * The {@link ProofOblInput} to prove.
    */
   private ProofOblInput problem;

   /**
    * Constructor.
    * @param problem The {@link ProofOblInput} to prove.
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    * @param method An optional {@link IMethod} from which the {@link Proof} was started.
    */
   public ProofOblInputEditorInput(ProofOblInput problem, 
                                   KeYEnvironment<?> environment, 
                                   IMethod method) {
      super(environment, method, problem.name());
      Assert.isNotNull(problem);
      this.problem = problem;
   }
   
   /**
    * Gives the {@link ProofOblInput} of this {@link ProofOblInputEditorInput}.
    * @return The {@link ProofOblInput} of this {@link ProofOblInputEditorInput}.
    */
   public ProofOblInput getProblem() {
      return problem;
   }   
}