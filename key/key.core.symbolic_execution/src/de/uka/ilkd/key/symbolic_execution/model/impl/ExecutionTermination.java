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

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionTermination}.
 * @author Martin Hentschel
 */
public class ExecutionTermination extends AbstractExecutionNode<SourceElement> implements IExecutionTermination {
   /**
    * Contains the exception variable which is used to check if the executed program in proof terminates normally.
    */
   private final IProgramVariable exceptionVariable;
   
   /**
    * The {@link Sort} of the uncaught exception.
    */
   private Sort exceptionSort;

   /**
    * The {@link TerminationKind}.
    */
   private TerminationKind terminationKind;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param exceptionVariable Contains the exception variable which is used to check if the executed program in proof terminates normally.
    * @param terminationKind The {@link TerminationKind} or {@code null} to compute it when it is requested the first time (normal or exceptional termination only).
    */
   public ExecutionTermination(ITreeSettings settings,
                               Node proofNode, 
                               IProgramVariable exceptionVariable, 
                               TerminationKind terminationKind) {
      super(settings, proofNode);
      this.exceptionVariable = exceptionVariable;
      this.terminationKind = terminationKind;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      switch (getTerminationKind()) {
         case EXCEPTIONAL : return INTERNAL_NODE_NAME_START + "uncaught " + exceptionSort + INTERNAL_NODE_NAME_END;
         case LOOP_BODY : return LOOP_BODY_TERMINATION_NODE_NAME;
         default : return NORMAL_TERMINATION_NODE_NAME;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramVariable getExceptionVariable() {
      return exceptionVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public TerminationKind getTerminationKind() {
      if (terminationKind == null) {
         terminationKind = isExceptionalTermination() ? TerminationKind.EXCEPTIONAL : TerminationKind.NORMAL;
      }
      return terminationKind;
   }

   /**
    * Checks if is an exceptional termination.
    * @return {@code true} exceptional termination, {@code false} normal termination.
    */
   protected boolean isExceptionalTermination() {
      Sort sort = getExceptionSort();
      return sort != null && !(sort instanceof NullSort);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Sort getExceptionSort() {
      if (exceptionSort == null) {
         exceptionSort = SymbolicExecutionUtil.lazyComputeExceptionSort(getProofNode(), exceptionVariable);
      }
      return exceptionSort;
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
   public String getElementType() {
      switch (getTerminationKind()) {
         case EXCEPTIONAL : return "Exceptional Termination";
         case LOOP_BODY : return "Loop Body Termination";
         default : return "Termination";
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isBranchVerified() {
      return SymbolicExecutionUtil.lazyComputeIsBranchVerified(getProofNode());
   }
}