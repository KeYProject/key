// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Special {@link SymbolicLayoutExtractor} for {@link IExecutionNode}s.
 * @author Martin Hentschel
 */
public class ExecutionNodeSymbolicLayoutExtractor extends SymbolicLayoutExtractor {
   /**
    * The {@link IExecutionNode} to extract memory layouts from.
    */
   private final IExecutionNode<?> executionNode;

   /**
    * Constructor.
    * @param executionNode The {@link IExecutionNode} to extract memory layouts from.
    */
   public ExecutionNodeSymbolicLayoutExtractor(IExecutionNode<?> executionNode) {
      super(executionNode.getProofNode(), 
            executionNode.getModalityPIO(),
            executionNode.getSettings().isUseUnicode(), 
            executionNode.getSettings().isUsePrettyPrinting());
      this.executionNode = executionNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeInitialStateName() {
      try {
         return SymbolicExecutionUtil.getRoot(executionNode).getName() + " resulting in " + computeCurrentStateName();
      }
      catch (ProofInputException e) {
         return e.getMessage();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeCurrentStateName() {
      try {
         return executionNode.getName();
      }
      catch (ProofInputException e) {
         return e.getMessage();
      }
   }
}