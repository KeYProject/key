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

package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionExceptionalMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionExceptionalMethodReturn}.
 * @author Martin Hentschel
 */
public class ExecutionExceptionalMethodReturn extends AbstractExecutionMethodReturn<Throw> implements IExecutionExceptionalMethodReturn {
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param methodCall The {@link IExecutionMethodCall} which is now returned.
    */
   public ExecutionExceptionalMethodReturn(ITreeSettings settings, 
                                           KeYMediator mediator, 
                                           Node proofNode,
                                           ExecutionMethodCall methodCall) {
      super(settings, mediator, proofNode, methodCall);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      String exceptionType;
      Expression expression = getActiveStatement().getExpression();
      if (expression instanceof ProgramVariable) {
         KeYJavaType type = ((ProgramVariable) expression).getKeYJavaType();
         exceptionType = type.getFullName();
      }
      else {
         exceptionType = expression.toString();
      }
      return INTERNAL_NODE_NAME_START + "throw " +
             exceptionType +
             INTERNAL_NODE_NAME_END;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IExecutionVariable[] lazyComputeVariables() {
      return SymbolicExecutionUtil.createExecutionVariables(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeSignature() throws ProofInputException {
      String methodName = getMethodCall().getName();
      return INTERNAL_NODE_NAME_START + "exceptional return" +
             (!JavaUtil.isTrimmedEmpty(methodName) ? " of " + methodName : "") +
             INTERNAL_NODE_NAME_END;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Exceptional Method Return";
   }
}