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

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionBranchCondition}.
 * @author Martin Hentschel
 */
public class ExecutionBranchCondition extends AbstractExecutionNode<SourceElement> implements IExecutionBranchCondition {
   /**
    * The optional additional branch label.
    */
   private final String additionalBranchLabel;
   
   /**
    * The {@link Term} which represents the branch condition.
    */
   private Term branchCondition;
   
   /**
    * The human readable branch condition.
    */
   private String formatedBranchCondition;
   
   /**
    * The path condition to reach this node.
    */
   private Term pathCondition;
   
   /**
    * The human readable path condition to reach this node.
    */
   private String formatedPathCondition;
   
   /**
    * Merged branch conditions.
    */
   private List<Node> mergedProofNodes;
   
   /**
    * Contains the merged branch conditions.
    */
   private Term[] mergedBranchCondtions;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param additionalBranchLabel The optional additional branch label.
    */
   public ExecutionBranchCondition(ITreeSettings settings, 
                                   KeYMediator mediator, 
                                   Node proofNode, 
                                   String additionalBranchLabel) {
      super(settings, mediator, proofNode);
      this.additionalBranchLabel = additionalBranchLabel;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      return getFormatedBranchCondition();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Branch Condition";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedBranchCondition() throws ProofInputException {
      if (branchCondition == null) {
         lazyComputeBranchCondition();
      }
      return formatedBranchCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isBranchConditionComputed() {
      return branchCondition != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getBranchCondition() throws ProofInputException {
      if (branchCondition == null) {
         lazyComputeBranchCondition();
      }
      return branchCondition;
   }

   /**
    * Computes the branch condition lazily when {@link #getBranchCondition()}
    * or {@link #getFormatedBranchCondition()} is called the first time.
    * @throws ProofInputException Occurred Exception
    */
   protected void lazyComputeBranchCondition() throws ProofInputException {
      if (!isDisposed()) {
         final Services services = getServices();
         // Compute branch condition
         if (isMergedBranchCondition()) {
            // Add all merged branch conditions
            Term[] mergedConditions = getMergedBranchCondtions();
            branchCondition = services.getTermBuilder().and(mergedBranchCondtions);
            // Simplify merged branch conditions
            if (mergedConditions.length >= 2) {
               branchCondition = SymbolicExecutionUtil.simplify(getProof(), branchCondition);
               branchCondition = SymbolicExecutionUtil.improveReadability(branchCondition, services);
            }
         }
         else {
            branchCondition = SymbolicExecutionUtil.computeBranchCondition(getProofNode(), true);
         }
         // Format branch condition
         formatedBranchCondition = formatTerm(branchCondition, services);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isPathConditionChanged() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getPathCondition() throws ProofInputException {
      if (pathCondition == null) {
         lazyComputePathCondition();
      }
      return pathCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedPathCondition() throws ProofInputException {
      if (formatedPathCondition == null) {
         lazyComputePathCondition();
      }
      return formatedPathCondition;
   }

   /**
    * Computes the path condition lazily when {@link #getPathCondition()}
    * or {@link #getFormatedPathCondition()} is called the first time.
    * @throws ProofInputException Occurred Exception
    */
   protected void lazyComputePathCondition() throws ProofInputException {
      if (!isDisposed()) {
         final Services services = getServices();
         // Get path to parent
         Term parentPath;
         if (getParent() != null) {
            parentPath = getParent().getPathCondition();
         }
         else {
            parentPath = services.getTermBuilder().tt();
         }
         // Add current branch condition to path
         pathCondition = services.getTermBuilder().and(parentPath, getBranchCondition());
         // Simplify path condition
         pathCondition = SymbolicExecutionUtil.simplify(getProof(), pathCondition);
         pathCondition = SymbolicExecutionUtil.improveReadability(pathCondition, services);
         // Format path condition
         formatedPathCondition = formatTerm(pathCondition, services);
      }
   }

   /**
    * Adds a merged proof {@link Node}.
    * @param node The proof {@link Node} to add.
    */
   public void addMergedProofNode(Node node) {
      if (mergedProofNodes == null) {
         mergedProofNodes = new LinkedList<Node>();
         mergedProofNodes.add(getProofNode());
      }
      mergedProofNodes.add(node);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Node[] getMergedProofNodes() {
      return mergedProofNodes != null ? mergedProofNodes.toArray(new Node[mergedProofNodes.size()]) : new Node[0];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term[] getMergedBranchCondtions() throws ProofInputException {
      if (mergedBranchCondtions == null) {
         mergedBranchCondtions = lazyComputeMergedBranchCondtions();
      }
      return mergedBranchCondtions;
   }

   /**
    * Computes the branch condition lazily when {@link #getMergedBranchCondtions()} 
    * is called the first time.
    * @throws ProofInputException Occurred Exception
    */
   protected Term[] lazyComputeMergedBranchCondtions() throws ProofInputException  {
      if (isMergedBranchCondition()) {
         Term[] result = new Term[mergedProofNodes.size()];
         Iterator<Node> iter = mergedProofNodes.iterator();
         for (int i = 0; i < result.length; i++) {
            result[i] = SymbolicExecutionUtil.computeBranchCondition(iter.next(), true);
         }
         return result;
      }
      else {
         return new Term[0];
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isMergedBranchCondition() {
      return mergedProofNodes != null && !mergedProofNodes.isEmpty();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalBranchLabel() {
      return additionalBranchLabel;
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
   protected PosInOccurrence lazyComputeModalityPIO() {
      return SymbolicExecutionUtil.findModalityWithMaxSymbolicExecutionLabelId(getProofNode().sequent());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SourceElement getActiveStatement() {
      Term modalityTerm = getModalityPIO().subTerm();
      SourceElement firstStatement = modalityTerm.javaBlock().program().getFirstElement();
      return NodeInfo.computeActiveStatement(firstStatement);
   }
}