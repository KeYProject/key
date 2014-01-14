// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link IExecutionMethodReturnValue}.
 * @author Martin Hentschel
 */
public class ExecutionMethodReturnValue extends AbstractExecutionElement implements IExecutionMethodReturnValue {
   /**
    * The return value.
    */
   private final Term returnValue;

   /**
    * The return value as human readable {@link String}.
    */
   private String returnValueString;
   
   /**
    * The optional condition.
    */
   private final Term condition;

   /**
    * The optional condition as human readable {@link String}.
    */
   private String conditionString;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param returnValue The return value.
    * @param condition The optional condition or {@code null} if no condition is available.
    */
   public ExecutionMethodReturnValue(ITreeSettings settings,
                                     KeYMediator mediator, 
                                     Node proofNode, 
                                     Term returnValue, 
                                     Term condition) {
      super(settings, mediator, proofNode);
      assert returnValue != null;
      this.returnValue = returnValue;
      this.condition = condition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Return Value";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      if (hasCondition()) {
         return getReturnValueString() + " {" + getConditionString() + "}";
      }
      else {
         return getReturnValueString();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getReturnValue() throws ProofInputException {
      return returnValue;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getReturnValueString() throws ProofInputException {
      if (returnValueString == null) {
         returnValueString = lazyComputeReturnValueString();
      }
      return returnValueString;
   }
   
   /**
    * Computes the human readable return value of this node lazily when {@link #getReturnValueString()}
    * is called the first time.
    * @return The human readable return value.
    */
   protected String lazyComputeReturnValueString() throws ProofInputException {
      return formatTerm(returnValue);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasCondition() throws ProofInputException {
      return condition != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getCondition() throws ProofInputException {
      return condition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getConditionString() throws ProofInputException {
      if (conditionString == null) {
         conditionString = lazyComputeConditionString();
      }
      return conditionString;
   }
   
   /**
    * Computes the human readable return value of this node lazily when {@link #getConditionString()}
    * is called the first time.
    * @return The human readable return value.
    */
   protected String lazyComputeConditionString() throws ProofInputException {
      if (hasCondition()) {
         return formatTerm(condition);
      }
      else {
         return null;
      }
   }
}