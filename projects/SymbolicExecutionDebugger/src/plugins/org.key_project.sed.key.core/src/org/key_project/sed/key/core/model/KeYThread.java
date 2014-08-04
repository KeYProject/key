/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.model;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDThread;
import org.key_project.sed.key.core.breakpoints.KeYBreakpointManager;
import org.key_project.sed.key.core.util.KeYModelUtil;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.sed.key.core.util.LogUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Services.ITermProgramVariableCollectorFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.TermProgramVariableCollectorKeepUpdatesForBreakpointconditions;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepOverSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepReturnSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * Implementation of {@link ISEDThread} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYThread extends AbstractSEDThread implements IKeYSEDDebugNode<IExecutionStart> {
   /**
    * The {@link IExecutionStart} to represent by this debug node.
    */
   private final IExecutionStart executionNode;

   /**
    * The contained children.
    */
   private IKeYSEDDebugNode<?>[] children;

   /**
    * The method call stack.
    */
   private IKeYSEDDebugNode<?>[] callStack;
   
   /**
    * The {@link IKeYSEDDebugNode} for which the auto mode was started the last time.
    */
   private IKeYSEDDebugNode<?> lastResumedKeyNode;
   
   /**
    * Listens for auto mode start and stop events.
    */
   private final AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStarted(ProofEvent e) {
         handleAutoModeStarted(e);
      }
      
      @Override
      public void autoModeStopped(ProofEvent e) {
         handleAutoModeStopped(e);
      }
   };
   
   /**
    * The up to know discovered {@link ISEDTermination} nodes.
    */
   private final Map<IExecutionTermination, ISEDTermination> knownTerminations = new HashMap<IExecutionTermination, ISEDTermination>();

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this branch condition is contained.
    * @param executionNode The {@link IExecutionStart} to represent by this debug node.
    */
   public KeYThread(KeYDebugTarget target, IExecutionStart executionNode) throws DebugException {
      super(target, true);
      Assert.isNotNull(executionNode);
      this.executionNode = executionNode;
      getMediator().addAutoModeListener(autoModeListener);
      target.registerDebugNode(this);
      initializeAnnotations();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYThread getThread() {
      return this;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYDebugTarget getDebugTarget() {
      return (KeYDebugTarget)super.getDebugTarget();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSEDDebugNode<?> getParent() throws DebugException {
      return (IKeYSEDDebugNode<?>)super.getParent();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSEDDebugNode<?>[] getChildren() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         IExecutionNode[] executionChildren = executionNode.getChildren();
         if (children == null) {
            children = KeYModelUtil.createChildren(this, executionChildren);
         }
         else if (children.length != executionChildren.length) { // Assumption: Only new children are added, they are never replaced or removed
            children = KeYModelUtil.updateChildren(this, children, executionChildren);
         }
         return children;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionStart getExecutionNode() {
      return executionNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      try {
         return executionNode.getName();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute name.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getPathCondition() throws DebugException {
      try {
         return executionNode.getFormatedPathCondition();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute path condition.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSEDDebugNode<?>[] getCallStack() throws DebugException {
      synchronized (this) {
         if (callStack == null) {
            callStack = KeYModelUtil.createCallStack(getDebugTarget(), executionNode.getCallStack()); 
         }
         return callStack;
      }
   }
   
   public SymbolicExecutionEnvironment<?> getEnvironment() {
      return getDebugTarget().getEnvironment();
   }
   
   public SymbolicExecutionTreeBuilder getBuilder() {
      return getEnvironment().getBuilder();
   }
   
   public KeYMediator getMediator() {
      return getEnvironment().getMediator();
   }
   
   public UserInterface getUi() {
      return getEnvironment().getUi();
   }
   
   public Proof getProof() {
      return getBuilder().getProof();
   }
   
   /**
    * Returns the used {@link KeYBreakpointManager}.
    * @return The used {@link KeYBreakpointManager}.
    */
   public KeYBreakpointManager getBreakpointManager() {
      return getDebugTarget().getBreakpointManager();
   }

   /**
    * When the auto mode is started.
    * @param e The {@link ProofEvent}.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      if (e.getSource() == getProof() && getMediator().isInAutoMode()) { // Sadly auto mode started events are misused and do not really indicate that a auto mode is running
         try {
            // Inform UI that the process is resumed
            super.resume();
            getDebugTarget().threadResumed(this);
         }
         catch (DebugException exception) {
            LogUtil.getLogger().logError(exception);
         }
      }
   }

   /**
    * When the auto mode has finished.
    * @param e The {@link ProofEvent}.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      if (e.getSource() == getProof() && !getMediator().isInAutoMode()) { // Sadly auto mode stopped events are misused and do not really indicate that a auto mode has stopped
         try {
            updateExecutionTree(getBuilder());
         }
         catch (Exception exception) {
            LogUtil.getLogger().logError(exception);
            LogUtil.getLogger().openErrorDialog(null, exception);
         }
         finally {
            try {
               super.suspend();
               getDebugTarget().threadSuspended(this);
            }
            catch (DebugException e1) {
               LogUtil.getLogger().logError(e1);
               LogUtil.getLogger().openErrorDialog(null, e1);
            }
         }
      }
   }

   /**
    * <p>
    * Updates the symbolic execution tree of the given {@link SymbolicExecutionTreeBuilder}
    * by calling {@link SymbolicExecutionTreeBuilder#analyse()}.
    * </p>
    * @param builder The {@link SymbolicExecutionTreeBuilder} to update.
    */
   protected void updateExecutionTree(SymbolicExecutionTreeBuilder builder) {
      if (getProof() != null) {
         // Update the symbolic execution tree, debug model is updated lazily via getters
         getBuilder().analyse();
      }
   }

   /**
    * Performs a disconnect on this {@link KeYThread}.
    * @throws DebugException Occurred Exception
    */
   public void disconnect() throws DebugException {
      getMediator().removeAutoModeListener(autoModeListener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      getMediator().removeAutoModeListener(autoModeListener);
      super.terminate();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return super.canResume() && 
             !getMediator().isInAutoMode() && // Only one proof completion per time is possible
             getUi().isAutoModeSupported(getProof()); // Otherwise Auto Mode is not available.
   }
   
   /**
    * Checks if resuming on the given {@link IKeYSEDDebugNode} is possible.
    * @param keyNode The {@link IKeYSEDDebugNode} to check.
    * @return {@code true} possible, {@code false} not possible.
    */
   public boolean canResume(IKeYSEDDebugNode<?> keyNode) {
      return canResume();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      resume(this);
   }

   /**
    * Resumes the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} to resume.
    * @throws DebugException Occurred Exception.
    */
   public void resume(IKeYSEDDebugNode<?> keyNode) throws DebugException {
      if (canResume()) {
         // Inform UI that the process is resumed
         super.resume();
         getDebugTarget().threadResumed(this);
         // Run auto mode
         runAutoMode(keyNode,
                     KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun(), 
                     keyNode != null ? SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()) : getProof().openEnabledGoals(),
                     false,
                     false);
      }
   }
   
   /**
    * Runs the auto mode in KeY until the maximal number of set nodes are executed.
    * @param keyNode The node for which the auto mode is started.
    * @param maximalNumberOfSetNodesToExecute The maximal number of set nodes to execute.
    * @param gaols The {@link Goal}s to work with.
    * @param stepOver Include step over stop condition?
    * @param stepReturn Include step return condition?
    */
   protected void runAutoMode(IKeYSEDDebugNode<?> keyNode,
                              int maximalNumberOfSetNodesToExecute, 
                              ImmutableList<Goal> goals, 
                              boolean stepOver,
                              boolean stepReturn) {
      lastResumedKeyNode = keyNode;
      Proof proof = getProof();
      // Set strategy to use
      StrategyProperties strategyProperties = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      proof.setActiveStrategy(new SymbolicExecutionStrategy.Factory().create(proof, strategyProperties));
      // Update stop condition
      CompoundStopCondition stopCondition = new CompoundStopCondition();
      stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(maximalNumberOfSetNodesToExecute));
      SymbolicExecutionBreakpointStopCondition breakpointParentStopCondition = getBreakpointManager().getBreakpointStopCondition();
      stopCondition.addChildren(breakpointParentStopCondition);
      proof.getServices().setFactory(createNewFactory(breakpointParentStopCondition));
      if (stepOver) {
         stopCondition.addChildren(new StepOverSymbolicExecutionTreeNodesStopCondition());
      }
      if (stepReturn) {
         stopCondition.addChildren(new StepReturnSymbolicExecutionTreeNodesStopCondition());
      }
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      getUi().startAutoMode(proof, goals);
   }


   /**
    * Creates a new factory that should be used by others afterwards.
    * @return The newly created {@link ITermProgramVariableCollectorFactory}.
    */
   protected ITermProgramVariableCollectorFactory createNewFactory(final SymbolicExecutionBreakpointStopCondition breakpointParentStopCondition) {
      ITermProgramVariableCollectorFactory programVariableCollectorFactory = new ITermProgramVariableCollectorFactory() {
         @Override
         public TermProgramVariableCollector create(Services services) {
            return new TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(services, breakpointParentStopCondition);
         }
      };
      return programVariableCollectorFactory;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return super.canSuspend() && 
             getMediator().isInAutoMode() && // Only if the auto mode is in progress
             getMediator().getSelectedProof() == getProof(); // And the auto mode handles this proof
   }
   
   /**
    * Checks if suspending on the given {@link IKeYSEDDebugNode} is possible.
    * @param keyNode The {@link IKeYSEDDebugNode} to check.
    * @return {@code true} possible, {@code false} not possible.
    */
   public boolean canSuspend(IKeYSEDDebugNode<?> keyNode) {
      return canSuspend();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      suspend(this);
   }
   
   /**
    * Suspends the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} to suspend.
    * @throws DebugException Occurred Exception.
    */
   public void suspend(IKeYSEDDebugNode<?> keyNode) throws DebugException {
      if (canSuspend()) {
         getUi().stopAutoMode();
         super.suspend();
         getDebugTarget().threadSuspended(this);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepInto() {
      return canStepInto(this);
   }

   /**
    * Checks if step into is possible.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step into action.
    * @return {@code true} can step into, {@code false} can not step into.
    */
   public boolean canStepInto(IKeYSEDDebugNode<?> keyNode) {
      return canResume(keyNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepInto() throws DebugException {
      stepInto(this);
   }

   /**
    * Executes the step into for the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step into.
    */
   public void stepInto(IKeYSEDDebugNode<?> keyNode) throws DebugException {
      if (canStepInto()) {
         runAutoMode(keyNode,
                     ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_FOR_ONE_STEP, 
                     SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()),
                     false,
                     false);
         super.stepInto();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepOver() {
      return canStepOver(this);
   }

   /**
    * Checks if step over is possible.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step over action.
    * @return {@code true} can step over, {@code false} can not step over.
    */
   public boolean canStepOver(IKeYSEDDebugNode<?> keyNode) {
      return canResume(keyNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepOver() throws DebugException {
      stepOver(this);
   }

   /**
    * Executes the step over for the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step over.
    */
   public void stepOver(IKeYSEDDebugNode<?> keyNode) throws DebugException {
      if (canStepOver()) {
         runAutoMode(keyNode,
                     KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun(), 
                     SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()),
                     true,
                     false);
         super.stepOver();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepReturn() {
      return canStepReturn(this);
   }

   /**
    * Checks if step return is possible.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step return action.
    * @return {@code true} can step return, {@code false} can not step return.
    */
   public boolean canStepReturn(IKeYSEDDebugNode<?> keyNode) {
      return canResume(keyNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepReturn() throws DebugException {
      stepReturn(this);
   }

   /**
    * Executes the step return for the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step return.
    */
   public void stepReturn(IKeYSEDDebugNode<?> keyNode) throws DebugException {
      if (canStepReturn()) {
         runAutoMode(keyNode,
                     KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun(), 
                     SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()),
                     false,
                     true);
         super.stepReturn();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getLeafsToSelect() throws DebugException {
      return collectLeafs(lastResumedKeyNode != null ? lastResumedKeyNode : this);
   }
   
   /**
    * Registers the given {@link ISEDTermination} on this node.
    * @param termination The {@link ISEDTermination} to register.
    */
   public void addTermination(ISEDTermination termination) {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         Assert.isNotNull(termination);
         @SuppressWarnings("unchecked")
         ISEDTermination oldTermination = knownTerminations.put(((IKeYSEDDebugNode<IExecutionTermination>)termination).getExecutionNode(), termination);
         Assert.isTrue(oldTermination == null);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDTermination[] getTerminations() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         ImmutableList<IExecutionTermination> executionTerminations = executionNode.getTerminations();
         ISEDTermination[] result = new ISEDTermination[executionTerminations.size()];
         int i = 0;
         for (IExecutionTermination executionTermination : executionTerminations) {
            ISEDTermination keyTermination = getTermination(executionTermination);
            if (keyTermination == null) {
               // Create new method return, its parent will be set later when the full child hierarchy is explored.
               keyTermination = (ISEDTermination)KeYModelUtil.createTermination(getDebugTarget(), this, null, executionTermination);
            }
            result[i] = keyTermination;
            i++;
         }
         return result;
      }
   }
   
   /**
    * Returns the {@link ISEDTermination} with the given {@link IExecutionTermination} if available.
    * @param executionTermination The {@link IExecutionTermination} to search its {@link ISEDTermination}.
    * @return The found {@link ISEDTermination} or {@code null} if not available.
    */
   public ISEDTermination getTermination(final IExecutionTermination executionTermination) {
      return knownTerminations.get(executionTermination);
   }
}