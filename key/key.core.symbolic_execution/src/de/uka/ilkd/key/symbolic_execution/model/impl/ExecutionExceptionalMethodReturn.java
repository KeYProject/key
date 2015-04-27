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

import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionExceptionalMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionExceptionalMethodReturn}.
 * @author Martin Hentschel
 */
public class ExecutionExceptionalMethodReturn extends AbstractExecutionMethodReturn<Throw> implements IExecutionExceptionalMethodReturn {
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param methodCall The {@link IExecutionMethodCall} which is now returned.
    */
   public ExecutionExceptionalMethodReturn(ITreeSettings settings, 
                                           Node proofNode,
                                           ExecutionMethodCall methodCall) {
      super(settings, proofNode, methodCall);
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
   protected IExecutionConstraint[] lazyComputeConstraints() {
      return SymbolicExecutionUtil.createExecutionConstraints(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeSignature() throws ProofInputException {
      String methodName = getMethodCall().getName();
      return INTERNAL_NODE_NAME_START + "exceptional return" +
             (!StringUtil.isTrimmedEmpty(methodName) ? " of " + methodName : "") +
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