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
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionLoopInvariant}.
 * @author Martin Hentschel
 */
public class ExecutionLoopInvariant extends AbstractExecutionNode<SourceElement> implements IExecutionLoopInvariant {
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionLoopInvariant(ITreeSettings settings, 
                                 KeYMediator mediator, 
                                 Node proofNode) {
      super(settings, mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getLoopInvariant().getPlainText(getServices(), getSettings().isUsePrettyPrinting(), getSettings().isUseUnicode()).trim();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Loop Invariant";
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
   protected IExecutionConstraint[] lazyComputeConstraints() {
      return SymbolicExecutionUtil.createExecutionConstraints(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public LoopInvariant getLoopInvariant() {
      return ((LoopInvariantBuiltInRuleApp)getProofNode().getAppliedRuleApp()).getInvariant();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public While getLoopStatement() {
      return ((LoopInvariantBuiltInRuleApp)getProofNode().getAppliedRuleApp()).getLoopStatement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isInitiallyValid() {
      boolean initiallyValid = false;
      if (getProofNode().childrenCount() >= 1) {
         initiallyValid = getProofNode().child(0).isClosed();
      }
      return initiallyValid;
   }
}