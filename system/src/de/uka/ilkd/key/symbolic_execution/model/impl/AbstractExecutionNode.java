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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeSymbolicLayoutExtractor;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBlockStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides a basic implementation of {@link IExecutionNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionNode<S extends SourceElement> extends AbstractExecutionElement implements IExecutionNode<S> {
   /**
    * Reference to the parent {@link IExecutionNode}.
    */
   private AbstractExecutionNode<?> parent;
   
   /**
    * Contains all child {@link IExecutionNode}s.
    */
   private final List<IExecutionNode<?>> children = new LinkedList<IExecutionNode<?>>();
   
   /**
    * The contained call stack.
    */
   private IExecutionNode<?>[] callStack;
   
   /**
    * The available {@link IExecutionConstraint}s.
    */
   private IExecutionConstraint[] constraints;
   
   /**
    * The variable value pairs of the current state.
    */
   private IExecutionVariable[] variables;
   
   /**
    * The variable value pairs of the current state under given conditions.
    */
   private final Map<Term, IExecutionVariable[]> conditionalVariables = new HashMap<Term, IExecutionVariable[]>();
   
   /**
    * The used {@link ExecutionNodeSymbolicLayoutExtractor}.
    */
   private ExecutionNodeSymbolicLayoutExtractor layoutExtractor;
   
   /**
    * The {@link PosInOccurrence} of the modality or its updates.
    */
   private PosInOccurrence modalityPIO;
   
   /**
    * The up to know discovered completed {@link IExecutionBlockStartNode}s.
    */
   private ImmutableList<IExecutionBlockStartNode<?>> completedBlocks = ImmutableSLList.nil();
   
   /**
    * The already computed block completion conditions.
    */
   private final Map<IExecutionBlockStartNode<?>, Term> blockCompletionConditions = new HashMap<IExecutionBlockStartNode<?>, Term>();

   /**
    * The already computed human readable block completion conditions.
    */
   private final Map<IExecutionBlockStartNode<?>, String> formatedBlockCompletionConditions = new HashMap<IExecutionBlockStartNode<?>, String>();
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionNode(ITreeSettings settings,
                                KeYMediator mediator, 
                                Node proofNode) {
      super(settings, mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public AbstractExecutionNode<?> getParent() {
      return parent;
   }

   /**
    * Sets the parent {@link AbstractExecutionNode}.
    * @param parent The parent {@link AbstractExecutionNode} to set.
    */
   public void setParent(AbstractExecutionNode<?> parent) {
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public AbstractExecutionNode<?>[] getChildren() {
      return children.toArray(new AbstractExecutionNode[children.size()]);
   }

   /**
    * Adds a new child {@link AbstractExecutionNode}.
    * @param child A new child {@link AbstractExecutionNode}.
    */
   public void addChild(AbstractExecutionNode<?> child) {
      if (child != null) {
         children.add(child);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isPathConditionChanged() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getPathCondition() throws ProofInputException {
      // Search path condition of the parent which is used by default.
      Term result = null;
      AbstractExecutionNode<?> parent = getParent();
      while (result == null && parent != null) {
         if (parent.isPathConditionChanged()) {
            result = parent.getPathCondition();
         }
         else {
            parent = parent.getParent();
         }
      }
      // Check if a path condition was found.
      return result != null ? result : getServices().getTermBuilder().tt();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedPathCondition() throws ProofInputException {
      // Search path condition of the parent which is used by default.
      String result = null;
      AbstractExecutionNode<?> parent = getParent();
      while (result == null && parent != null) {
         if (parent.isPathConditionChanged()) {
            result = parent.getFormatedPathCondition();
         }
         else {
            parent = parent.getParent();
         }
      }
      // Check if a path condition was found.
      if (!isDisposed()) {
         return result != null ? result : getServices().getTermBuilder().tt().toString();
      }
      else {
         return result;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionNode<?>[] getCallStack() {
      return callStack;
   }
   
   /**
    * Sets the call stack.
    * @param callStack The call stack.
    */
   public void setCallStack(IExecutionNode<?>[] callStack) {
      this.callStack = callStack;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionConstraint[] getConstraints() {
      synchronized (this) {
         if (constraints == null) {
            constraints = lazyComputeConstraints();
         }
         return constraints;
      }
   }

   /**
    * Computes the constraints lazily when {@link #getConstraints()} is 
    * called the first time.
    * @return The {@link IExecutionConstraint}s of the current state.
    */
   protected abstract IExecutionConstraint[] lazyComputeConstraints();
   
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("unchecked")
   @Override
   public S getActiveStatement() {
      return (S)getProofNodeInfo().getActiveStatement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PositionInfo getActivePositionInfo() {
      return getActiveStatement().getPositionInfo();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable[] getVariables() throws ProofInputException {
      synchronized (this) {
         if (variables == null) {
            variables = lazyComputeVariables();
         }
         return variables;
      }
   }

   /**
    * Computes the variables lazily when {@link #getVariables()} is 
    * called the first time.
    * @return The {@link IExecutionVariable}s of the current state.
    * @throws ProofInputException 
    */
   protected IExecutionVariable[] lazyComputeVariables() throws ProofInputException {
      return SymbolicExecutionUtil.createExecutionVariables(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable[] getVariables(Term condition) throws ProofInputException {
      synchronized (this) {
         IExecutionVariable[] result = conditionalVariables.get(condition);
         if (result == null) {
            result = lazyComputeVariables(condition);
            conditionalVariables.put(condition, result);
         }
         return result;
      }
   }

   /**
    * Computes the variables lazily when {@link #getVariables(Term)} is 
    * called the first time.
    * @param condition A {@link Term} specifying some additional constraints to consider.
    * @return The {@link IExecutionVariable}s of the current state under the given condition.
    * @throws ProofInputException 
    */
   protected IExecutionVariable[] lazyComputeVariables(Term condition) throws ProofInputException {
      return SymbolicExecutionUtil.createExecutionVariables(this, condition);
   }

   /**
    * Returns the used {@link ExecutionNodeSymbolicLayoutExtractor}.
    * @return The used {@link ExecutionNodeSymbolicLayoutExtractor}.
    * @throws ProofInputException Occurred Exception.
    */
   public ExecutionNodeSymbolicLayoutExtractor getLayoutExtractor() throws ProofInputException {
      synchronized (this) {
         if (layoutExtractor == null) {
            layoutExtractor = lazyComputeLayoutExtractor();
         }
         return layoutExtractor;
      }
   }

   /**
    * Instantiates the used {@link ExecutionNodeSymbolicLayoutExtractor} lazily
    * when {@link #getLayoutExtractor()} is called the first time.
    * @return The created {@link ExecutionNodeSymbolicLayoutExtractor}.
    * @throws ProofInputException Occurred Exception.
    */
   protected ExecutionNodeSymbolicLayoutExtractor lazyComputeLayoutExtractor() throws ProofInputException {
      ExecutionNodeSymbolicLayoutExtractor result = new ExecutionNodeSymbolicLayoutExtractor(this);
      result.analyse();
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getLayoutsCount() throws ProofInputException {
      return getLayoutExtractor().getLayoutsCount();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicLayout getInitialLayout(int layoutIndex) throws ProofInputException {
      return getLayoutExtractor().getInitialLayout(layoutIndex);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicLayout getCurrentLayout(int layoutIndex) throws ProofInputException {
      return getLayoutExtractor().getCurrentLayout(layoutIndex);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicEquivalenceClass> getLayoutsEquivalenceClasses(int layoutIndex) throws ProofInputException {
      return getLayoutExtractor().getEquivalenceClasses(layoutIndex);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PosInOccurrence getModalityPIO() {
      if (modalityPIO == null) {
         modalityPIO = lazyComputeModalityPIO();
      }
      return modalityPIO;
   }

   /**
    * Computes the {@link PosInOccurrence} lazily when {@link #getModalityPIO()} is 
    * called the first time.
    * @return The {@link PosInOccurrence}s of the modality or its updates.
    */
   protected PosInOccurrence lazyComputeModalityPIO() {
      PosInOccurrence originalPio = getProofNode().getAppliedRuleApp().posInOccurrence();
      // Try to go back to the parent which provides the updates
      PosInOccurrence pio = originalPio;
      Term term = pio.subTerm();
      if (!pio.isTopLevel() && term.op() != UpdateApplication.UPDATE_APPLICATION) {
         pio = pio.up();
         term = pio.subTerm();
      }
      // Return found updates or the original pio otherwise
      return term.op() == UpdateApplication.UPDATE_APPLICATION ? 
             pio : 
             originalPio;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<IExecutionBlockStartNode<?>> getCompletedBlocks() {
      return completedBlocks;
   }
   
   /**
    * Registers the given {@link IExecutionBlockStartNode}.
    * @param completedBlock The {@link IExecutionBlockStartNode} to register.
    */
   public void addCompletedBlock(IExecutionBlockStartNode<?> completedBlock) {
      if (completedBlock != null && !completedBlocks.contains(completedBlock)) {
         completedBlocks = completedBlocks.append(completedBlock);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getBlockCompletionCondition(IExecutionBlockStartNode<?> completedNode) throws ProofInputException {
      Term result = blockCompletionConditions.get(completedNode);
      if (result == null) {
         result = (Term) lazyComputeBlockCompletionCondition(completedNode, false);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedBlockCompletionCondition(IExecutionBlockStartNode<?> completedNode) throws ProofInputException {
      String result = formatedBlockCompletionConditions.get(completedNode);
      if (result == null) {
         result = (String) lazyComputeBlockCompletionCondition(completedNode, true);
      }
      return result;
   }

   /**
    * Computes the condition lazily when {@link #getBlockCompletionCondition(IExecutionNode)}
    * or {@link #getFormatedBlockCompletionCondition(IExecutionNode)} is called the first time.
    * @param completedNode The completed {@link IExecutionNode} for which the condition is requested.
    * @param returnFormatedCondition {@code true} formated condition is returned, {@code false} {@link Term} is returned.
    * @throws ProofInputException Occurred Exception
    */
   protected Object lazyComputeBlockCompletionCondition(IExecutionBlockStartNode<?> completedNode, boolean returnFormatedCondition) throws ProofInputException {
      if (!isDisposed() && completedBlocks.contains(completedNode)) {
         final Services services = getServices();
         // Collect branch conditions
         List<Term> bcs = new LinkedList<Term>();
         AbstractExecutionNode<?> parent = getParent();
         while (parent != null && parent != completedNode) {
            if (parent instanceof IExecutionBranchCondition) {
               bcs.add(((IExecutionBranchCondition)parent).getBranchCondition());
            }
            parent = parent.getParent();
         }
         // Add current branch condition to path
         Term condition = services.getTermBuilder().and(bcs);
         // Simplify path condition
         condition = SymbolicExecutionUtil.simplify(getProof(), condition);
         condition = SymbolicExecutionUtil.improveReadability(condition, services);
         // Format path condition
         String formatedCondition = formatTerm(condition, services);
         // Update maps
         blockCompletionConditions.put(completedNode, condition);
         formatedBlockCompletionConditions.put(completedNode, formatedCondition);
         return returnFormatedCondition ? formatedCondition : condition;
      }
      else {
         return null;
      }
   }
}