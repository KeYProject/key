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

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.key_project.keyide.ui.handlers.BreakpointToggleHandler;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISENodeLink;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.impl.AbstractSEThread;
import org.key_project.sed.core.model.memory.SEMemoryBranchCondition;
import org.key_project.sed.core.util.SEPreorderIterator;
import org.key_project.sed.key.core.breakpoints.KeYBreakpointManager;
import org.key_project.sed.key.core.util.KeYModelUtil;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Services.ITermProgramVariableCollectorFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.TermProgramVariableCollectorKeepUpdatesForBreakpointconditions;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder.SymbolicExecutionCompletions;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionNode;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepOverSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepReturnSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Implementation of {@link ISEThread} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYThread extends AbstractSEThread implements IKeYSENode<IExecutionStart> {
   /**
    * The {@link IExecutionStart} to represent by this debug node.
    */
   private final IExecutionStart executionNode;

   /**
    * The contained children.
    */
   private IKeYSENode<?>[] children;

   /**
    * The method call stack.
    */
   private IKeYSENode<?>[] callStack;
   
   /**
    * The {@link IKeYSENode} for which the auto mode was started the last time.
    */
   private IKeYSENode<?> lastResumedKeyNode;
   
   /**
    * The constraints
    */
   private KeYConstraint[] constraints;
   
   /**
    * The contained KeY variables.
    */
   private KeYVariable[] variables;
   
   /**
    * Indicates if {@link #getLeafsToSelect()} will return the leaf nodes
    * or an empty array otherwise. An empty array is returned in case
    * of interactive verification whereas new leafs to select are supported
    * when the auto mode was started via the debug API.
    * <p>
    * The value is initially {@code true} because after a launch the debug API
    * asks for the initial elements to select.
    */
   private boolean leafsToSelectAvailable = true;
   
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
    * Listens for proof changes
    */
   private final ProofTreeListener proofChangedListener = new ProofTreeAdapter() {
      @Override
      public void proofPruned(ProofTreeEvent e) {
        handleProofPruned(e);  
      }

      @Override
      public void proofGoalsAdded(ProofTreeEvent e) { 
         handleGoalsAdded(e);
      }
   };
   
   /**
    * The up to know discovered {@link ISETermination} nodes.
    */
   private final Map<IExecutionTermination, ISETermination> knownTerminations = new HashMap<IExecutionTermination, ISETermination>();
   
   /**
    * The conditions under which a group ending in this node starts.
    */
   private SEMemoryBranchCondition[] groupStartConditions;

   /**
    * The {@link State} specifying if breakpoints are activated or not.
    */
   private State breakpointsActivatedState;

   /**
    * Listens for changes on {@link #breakpointsActivatedState}.
    */
   private final IStateListener breakpointsActivatedStateListener = new IStateListener() {
      @Override
      public void handleStateChange(State state, Object oldValue) {
         hnadleStopAtBreakpointsChanged(state, oldValue);
      }
   };

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this branch condition is contained.
    * @param executionNode The {@link IExecutionStart} to represent by this debug node.
    */
   public KeYThread(KeYDebugTarget target, IExecutionStart executionNode) throws DebugException {
      super(target, true);
      Assert.isNotNull(executionNode);
      this.executionNode = executionNode;
      initializeBreakpointToggle();
      getProofControl().addAutoModeListener(autoModeListener);
      Proof proof = getProof();
      proof.addProofTreeListener(proofChangedListener);
      target.registerDebugNode(this);
      initializeAnnotations();
      configureProofForInteractiveVerification(proof);
   }

   /**
    * Initializes {@link #breakpointsActivatedState}.
    */
   protected void initializeBreakpointToggle() {
      ICommandService service = (ICommandService)PlatformUI.getWorkbench().getService(ICommandService.class);
      if (service != null) {
         Command command = service.getCommand(BreakpointToggleHandler.COMMAND_ID);
         if (command != null) {
            breakpointsActivatedState = command.getState(RegistryToggleState.STATE_ID);
            if (breakpointsActivatedState != null) {
               breakpointsActivatedState.addListener(breakpointsActivatedStateListener);
            }
         }
      }
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
   public IKeYSENode<?> getParent() throws DebugException {
      return (IKeYSENode<?>)super.getParent();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSENode<?>[] getChildren() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         IExecutionNode<?>[] executionChildren = executionNode.getChildren();
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
   public IKeYSENode<?>[] getCallStack() throws DebugException {
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
   
   public UserInterfaceControl getUi() {
      return getEnvironment().getUi();
   }
   
   public ProofControl getProofControl() {
      return getEnvironment().getProofControl();
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
    * When the proof was pruned.
    * @param e The event.
    */
   protected void handleProofPruned(ProofTreeEvent e) {
	  HashSet<AbstractExecutionNode<?>> deletedExNodes = getBuilder().prune(e.getNode());	 
	  SEPreorderIterator iter = new SEPreorderIterator(this);
	  // iterate over key node tree and remove all pruned method returns
	  try {
      while (iter.hasNext()) {
           ISEDebugElement keyNode = iter.next();
           if (keyNode instanceof KeYMethodCall) {
              ArrayList<IExecutionBaseMethodReturn<?>> markedForDeletion = new ArrayList<IExecutionBaseMethodReturn<?>>();
              for (IExecutionBaseMethodReturn<?> exReturn : ((KeYMethodCall) keyNode).getAllMethodReturns().keySet()) {
                  if (deletedExNodes.contains(exReturn)) {
                      markedForDeletion.add(exReturn);
                  }
              }
              for (IExecutionBaseMethodReturn<?> exReturn : markedForDeletion) {
                  ((KeYMethodCall) keyNode).removeMethodReturn(exReturn);
              }
          }
        }
	  } catch (DebugException e1) {
      LogUtil.getLogger().logError(e1);
	  }
	  // remove all pruned execution nodes that terminate the start node
      ArrayList<IExecutionTermination> toBeDeleted = new ArrayList<IExecutionTermination>();
      for (IExecutionTermination termination : knownTerminations.keySet()) {
    	  if (deletedExNodes.contains(termination)) {
    		  toBeDeleted.add(termination);
    	  }
      }
      for (IExecutionTermination termination : toBeDeleted) {
    	  knownTerminations.remove(termination);
      }
      // remove all pruned execution nodes from the debug target
      for (IExecutionNode<?> exNode : deletedExNodes) {
    	  getDebugTarget().removeExecutionNode(exNode);
      }
      try {
         super.suspend();
      } catch (DebugException exception) {
         LogUtil.getLogger().logError(exception);
      }
   }
   
   /**
    * handles event when goals are added to the prooftree.
    * @param e The {@link ProofTreeEvent}
    */
   protected void handleGoalsAdded(ProofTreeEvent e) {
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
         }
         catch (DebugException e1) {
            LogUtil.getLogger().logError(e1);
            LogUtil.getLogger().openErrorDialog(null, e1);
         }
      }
   }

   /**
    * When the auto mode is started.
    * @param e The {@link ProofEvent}.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      Proof proof = getProof();
      if (e.getSource() == proof && getProofControl().isInAutoMode()) { // Sadly auto mode started events are misused and do not really indicate that a auto mode is running
         try {
            if (proof != null) {
               proof.removeProofTreeListener(proofChangedListener);
            }
            // Inform UI that the process is resumed
            super.resume();
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
      Proof proof = getProof();
      configureProofForInteractiveVerification(proof);
      if (e.getSource() == proof && !getProofControl().isInAutoMode()) { // Sadly auto mode stopped events are misused and do not really indicate that a auto mode has stopped
         try {
            updateExecutionTree(getBuilder());
         }
         catch (Exception exception) {
            LogUtil.getLogger().logError(exception);
            LogUtil.getLogger().openErrorDialog(null, exception);
         }
         finally {
            try {
               if (proof != null && !proof.isDisposed()) {
                  proof.addProofTreeListener(proofChangedListener);
                  
               }
               super.suspend();
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
    * @throws DebugException Occurred Exception.
    */
   protected void updateExecutionTree(SymbolicExecutionTreeBuilder builder) throws DebugException {
      if (getProof() != null) {
         // Update the symbolic execution tree, debug model is updated lazily via getters
         SymbolicExecutionCompletions completions = getBuilder().analyse();
         handleCompletions(completions);
      }
   }
   
   /**
    * This methods handles all completions, e.g. by collapsing their debug node representations.
    * @param completions The detected {@link SymbolicExecutionCompletions}.
    * @throws DebugException Occurred Exception.
    */
   protected void handleCompletions(SymbolicExecutionCompletions completions) throws DebugException {
// TODO: This methods does currently nothing until collapsing is supported by the SED.
      // Collapse all completed blocks
//      for (IExecutionNode<?> blockCompletion : completions.getBlockCompletions()) {
//         for (IExecutionNode<?> completedBlock : blockCompletion.getCompletedBlocks()) {
//            IKeYSEDDebugNode<?> keyNode = getDebugTarget().ensureDebugNodeIsCreated(completedBlock);
//            if (keyNode instanceof ISEDGroupable) {
//               ((ISEDGroupable) keyNode).setCollapsed(true);
//            }
//         }
//      }
////       Collapse all returned methods
//      for (IExecutionBaseMethodReturn<?> methodReturn : completions.getMethodReturns()) {
//         IExecutionMethodCall methodCall = methodReturn.getMethodCall();
//         IKeYSEDDebugNode<?> keyNode = getDebugTarget().ensureDebugNodeIsCreated(methodCall);
//         if (keyNode instanceof ISEDGroupable) {
//            ((ISEDGroupable) keyNode).setCollapsed(true);
//         }
//      }
   }

   /**
    * Performs a disconnect on this {@link KeYThread}.
    * @throws DebugException Occurred Exception
    */
   public void disconnect() throws DebugException {
      getProofControl().removeAutoModeListener(autoModeListener);
      getProof().removeProofTreeListener(proofChangedListener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      getProofControl().removeAutoModeListener(autoModeListener);
      getProof().removeProofTreeListener(proofChangedListener);
      if (breakpointsActivatedState != null) {
         breakpointsActivatedState.removeListener(breakpointsActivatedStateListener);
      }
      super.terminate();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return super.canResume() && 
             !getProofControl().isInAutoMode() && // Only one proof completion per time is possible
             getProofControl().isAutoModeSupported(getProof()); // Otherwise Auto Mode is not available.
   }
   
   /**
    * Checks if resuming on the given {@link IKeYSENode} is possible.
    * @param keyNode The {@link IKeYSENode} to check.
    * @return {@code true} possible, {@code false} not possible.
    */
   public boolean canResume(IKeYSENode<?> keyNode) {
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
    * Resumes the given {@link IKeYSENode}.
    * @param keyNode The {@link IKeYSENode} to resume.
    * @throws DebugException Occurred Exception.
    */
   public void resume(IKeYSENode<?> keyNode) throws DebugException {
      if (canResume()) {
         // Inform UI that the process is resumed
         super.resume();
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
    * @param goals The {@link Goal}s to work with.
    * @param stepOver Include step over stop condition?
    * @param stepReturn Include step return condition?
    */
   protected void runAutoMode(IKeYSENode<?> keyNode,
                              int maximalNumberOfSetNodesToExecute, 
                              ImmutableList<Goal> goals, 
                              boolean stepOver,
                              boolean stepReturn) {
      leafsToSelectAvailable = true;
      lastResumedKeyNode = keyNode;
      Proof proof = getProof();
      // Configure proof
      configureProof(proof, maximalNumberOfSetNodesToExecute, stepOver, stepReturn);
      // Run proof
      getProofControl().startAutoMode(proof, goals);
   }
   
   /**
    * Configures {@link #getProof()} with settings for interactive verification.
    * @param proof The {@link Proof} to configure.
    */
   protected void configureProofForInteractiveVerification(Proof proof) {
      if (proof != null && !proof.isDisposed()) {
         // Set default strategy settings
         SymbolicExecutionUtil.initializeStrategy(getBuilder());
         // Remove custom strategy because it destroys the behavior of the model search arithmetic treatment.
         proof.getSettings().getStrategySettings().setCustomApplyStrategyGoalChooser(null);
         if (isStopAtBreakpointsActivated()) {
            proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(getBreakpointManager().getBreakpointStopCondition());
         }
         else {
            proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(null);
         }
      }
   }

   /**
    * When the stop at breakpoints state has changed.
    * @param state The changed {@link State}.
    * @param oldValue The old value.
    */
   protected void hnadleStopAtBreakpointsChanged(State state, Object oldValue) {
      Proof proof = getProof();
      if (proof != null && !proof.isDisposed() && isSuspended()) {
         if (isStopAtBreakpointsActivated()) {
            proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(getBreakpointManager().getBreakpointStopCondition());
         }
         else {
            proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(null);
         }
      }
   }

   /**
    * Checks if {@link #breakpointsActivatedState} is selected or not.
    * @return {@code true} stop at breakpoints, {@code false} do not stop at breakpoints.
    */
   protected boolean isStopAtBreakpointsActivated() {
      Object value = breakpointsActivatedState.getValue();
      return value instanceof Boolean && ((Boolean)value).booleanValue();
   }
   
   /**
    * Configures the given {@link Proof}.
    * @param proof The {@link Proof} to configure.
    * @param maximalNumberOfSetNodesToExecute The maximal number of set nodes to execute.
    * @param stepOver Include step over stop condition?
    * @param stepReturn Include step return condition?
    */
   protected void configureProof(Proof proof, int maximalNumberOfSetNodesToExecute, boolean stepOver, boolean stepReturn) {
      if (proof != null && !proof.isDisposed()) {
         // Set strategy to use
         SymbolicExecutionUtil.initializeStrategy(getBuilder());
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
         proof.getSettings().getStrategySettings().setCustomApplyStrategyGoalChooser(new SymbolicExecutionGoalChooser());
         proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      }
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
             getProofControl().isInAutoMode() && // Only if the auto mode is in progress
             getProofControl().isAutoModeSupported(getProof()); // And the auto mode handles this proof
   }
   
   /**
    * Checks if suspending on the given {@link IKeYSENode} is possible.
    * @param keyNode The {@link IKeYSENode} to check.
    * @return {@code true} possible, {@code false} not possible.
    */
   public boolean canSuspend(IKeYSENode<?> keyNode) {
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
    * Suspends the given {@link IKeYSENode}.
    * @param keyNode The {@link IKeYSENode} to suspend.
    * @throws DebugException Occurred Exception.
    */
   public void suspend(IKeYSENode<?> keyNode) throws DebugException {
      if (canSuspend()) {
         getProofControl().stopAndWaitAutoMode();
         super.suspend();
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
    * @param keyNode The {@link IKeYSENode} which requests the step into action.
    * @return {@code true} can step into, {@code false} can not step into.
    */
   public boolean canStepInto(IKeYSENode<?> keyNode) {
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
    * Executes the step into for the given {@link IKeYSENode}.
    * @param keyNode The {@link IKeYSENode} which requests the step into.
    */
   public void stepInto(IKeYSENode<?> keyNode) throws DebugException {
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
    * @param keyNode The {@link IKeYSENode} which requests the step over action.
    * @return {@code true} can step over, {@code false} can not step over.
    */
   public boolean canStepOver(IKeYSENode<?> keyNode) {
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
    * Executes the step over for the given {@link IKeYSENode}.
    * @param keyNode The {@link IKeYSENode} which requests the step over.
    */
   public void stepOver(IKeYSENode<?> keyNode) throws DebugException {
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
    * @param keyNode The {@link IKeYSENode} which requests the step return action.
    * @return {@code true} can step return, {@code false} can not step return.
    */
   public boolean canStepReturn(IKeYSENode<?> keyNode) {
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
    * Executes the step return for the given {@link IKeYSENode}.
    * @param keyNode The {@link IKeYSENode} which requests the step return.
    */
   public void stepReturn(IKeYSENode<?> keyNode) throws DebugException {
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
   public ISENode[] getLeafsToSelect() throws DebugException {
      if (leafsToSelectAvailable) {
         leafsToSelectAvailable = false;
         return collectLeafs(lastResumedKeyNode != null ? lastResumedKeyNode : this);
      }
      else {
         return new ISENode[0];
      }
   }
   
   /**
    * Registers the given {@link ISETermination} on this node.
    * @param termination The {@link ISETermination} to register.
    */
   public void addTermination(ISETermination termination) {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         Assert.isNotNull(termination);
         @SuppressWarnings("unchecked")
         ISETermination oldTermination = knownTerminations.put(((IKeYSENode<IExecutionTermination>)termination).getExecutionNode(), termination);
         Assert.isTrue(oldTermination == null);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISETermination[] getTerminations() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         ImmutableList<IExecutionTermination> executionTerminations = executionNode.getTerminations();
         ISETermination[] result = new ISETermination[executionTerminations.size()];
         int i = 0;
         for (IExecutionTermination executionTermination : executionTerminations) {
            ISETermination keyTermination = getTermination(executionTermination);
            if (keyTermination == null) {
               // Create new method return, its parent will be set later when the full child hierarchy is explored.
               keyTermination = (ISETermination)KeYModelUtil.createTermination(getDebugTarget(), this, null, executionTermination);
            }
            result[i] = keyTermination;
            i++;
         }
         return result;
      }
   }
   
   /**
    * Returns the {@link ISETermination} with the given {@link IExecutionTermination} if available.
    * @param executionTermination The {@link IExecutionTermination} to search its {@link ISETermination}.
    * @return The found {@link ISETermination} or {@code null} if not available.
    */
   public ISETermination getTermination(final IExecutionTermination executionTermination) {
      return knownTerminations.get(executionTermination);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasConstraints() throws DebugException {
      return !isTerminated() && super.hasConstraints();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYConstraint[] getConstraints() throws DebugException {
      synchronized (this) {
         if (constraints == null) {
            constraints = KeYModelUtil.createConstraints(this, executionNode);
         }
         return constraints;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasVariables() throws DebugException {
      try {
         return getDebugTarget().getLaunchSettings().isShowVariablesOfSelectedDebugNode() &&
                !executionNode.isDisposed() && 
                SymbolicExecutionUtil.canComputeVariables(executionNode, executionNode.getServices()) &&
                super.hasVariables();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYVariable[] getVariables() throws DebugException {
      synchronized (this) {
         if (variables == null) {
            variables = KeYModelUtil.createVariables(this, executionNode);
         }
         return variables;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getLineNumber() throws DebugException {
      return -1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharStart() throws DebugException {
      return -1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharEnd() throws DebugException {
      return -1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getSourcePath() {
      IMethod method = getDebugTarget().getLaunchSettings().getMethod();
      if (method != null) {
         File localFile = ResourceUtil.getLocation(method.getResource());
         return localFile != null ? localFile.getAbsolutePath() : null;
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEMemoryBranchCondition[] getGroupStartConditions() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         if (groupStartConditions == null) {
            groupStartConditions = KeYModelUtil.createCompletedBlocksConditions(this);
         }
         return groupStartConditions;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setParent(ISENode parent) {
      super.setParent(parent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isTruthValueTracingEnabled() {
      return SymbolicExecutionJavaProfile.isTruthValueTracingEnabled(getExecutionNode().getProof());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISENodeLink[] getOutgoingLinks() throws DebugException {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISENodeLink[] getIncomingLinks() throws DebugException {
      return null;
   }
}