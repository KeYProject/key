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
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionUseOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionUseOperationContract}.
 * @author Martin Hentschel
 */
public class ExecutionUseOperationContract extends AbstractExecutionStateNode<SourceElement> implements IExecutionUseOperationContract {
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionUseOperationContract(KeYMediator mediator, Node proofNode) {
      super(mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getContract().getPlainText(getServices());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Contract getContract() {
      return ((AbstractContractRuleApp)getProofNode().getAppliedRuleApp()).getInstantiation();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramMethod getContractProgramMethod() {
      Contract contract = getContract();
      if (contract instanceof OperationContract) {
         return ((OperationContract)contract).getTarget();
      }
      else {
         return null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Use Operation Contract";
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
   public boolean isPreconditionComplied() {
      boolean complied = false;
      if (getProofNode().childrenCount() >= 3) {
         complied = getProofNode().child(2).isClosed();
      }
      return complied;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasNotNullCheck() {
      return getProofNode().childrenCount() >= 4;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isNotNullCheckComplied() {
      if (hasNotNullCheck()) {
         return getProofNode().child(3).isClosed();
      }
      else {
         return false;
      }
   }
}