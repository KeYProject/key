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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionMethodCall}.
 * @author Martin Hentschel
 */
public class ExecutionMethodCall extends AbstractExecutionStateNode<MethodBodyStatement> implements IExecutionMethodCall {
   /**
    * The up to know discovered {@link IExecutionMethodReturn}s.
    */
   private ImmutableList<IExecutionMethodReturn> methodReturns = ImmutableSLList.nil();

   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionMethodCall(ITreeSettings settings,
                              KeYMediator mediator, 
                              Node proofNode) {
      super(settings, mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      MethodReference explicitConstructorMR = getExplicitConstructorMethodReference();
      return explicitConstructorMR != null ?
             explicitConstructorMR.toString() :
             getMethodReference().toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isImplicitConstructor() {
      return KeYTypeUtil.isImplicitConstructor(getProgramMethod());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public MethodReference getExplicitConstructorMethodReference() {
      IProgramMethod explicitConstructor = getExplicitConstructorProgramMethod();
      if (explicitConstructor != null) {
         MethodReference mr = getMethodReference();
         return new MethodReference(mr.getArguments(), explicitConstructor.getProgramElementName(), null); // Ignore the prefix because it is ugly if a constructor is called on an object not part of the symbolic execution tree.
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramMethod getExplicitConstructorProgramMethod() {
      IProgramMethod pm = getProgramMethod();
      if (KeYTypeUtil.isImplicitConstructor(pm)) {
         return KeYTypeUtil.findExplicitConstructor(getServices(), pm);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public MethodReference getMethodReference() {
      return getActiveStatement().getMethodReference();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramMethod getProgramMethod() {
      return getActiveStatement().getProgramMethod(getServices());
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
   public String getElementType() {
      return "Method Call";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<IExecutionMethodReturn> getMethodReturns() {
      return methodReturns;
   }
   
   /**
    * Registers the given {@link IExecutionMethodReturn}.
    * @param methodReturn The {@link IExecutionMethodReturn} to register.
    */
   public void addMethodReturn(IExecutionMethodReturn methodReturn) {
      if (methodReturn != null) {
         assert methodReturn.getMethodCall() == this;
         methodReturns = methodReturns.prepend(methodReturn);
      }
   }
}