/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IMethod;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.key.core.launch.KeYLaunchSettings;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.core.util.LogUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepOverSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepReturnSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Implementation if {@link ISEDDebugTarget} which uses KeY to symbolically
 * debug a program.
 * @author Martin Hentschel
 */
public class KeYDebugTarget extends SEDMemoryDebugTarget {
   /**
    * The used model identifier.
    */
   public static final String MODEL_IDENTIFIER = "org.key_project.sed.key.core";
   
   /**
    * The {@link KeYLaunchSettings} to use.
    */
   private KeYLaunchSettings launchSettings;
   
   /**
    * The only contained child thread.
    */
   private KeYThread thread;
   
   /**
    * Listens for changes on the auto mode of KeY Main Frame,.
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
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
    * The {@link SymbolicExecutionEnvironment} which provides all relevant
    * information for symbolic execution.
    */
   private SymbolicExecutionEnvironment<?> environment;

   /**
    * Maps an {@link IExecutionNode} to its representation in the debug model.
    */
   private Map<IExecutionNode, IKeYSEDDebugNode<?>> executionToDebugMapping = new HashMap<IExecutionNode, IKeYSEDDebugNode<?>>();
   
   /**
    * Constructor.
    * @param launch The parent {@link ILaunch}.
    * @param mediator the used {@link KeYMediator} during proof.
    * @param proof The {@link Proof} in KeY to treat.
    * @param launchSettings The {@link KeYLaunchSettings} to use.
    * @throws DebugException Occurred Exception
    */
   public KeYDebugTarget(ILaunch launch,
                         SymbolicExecutionEnvironment<?> environment,
                         KeYLaunchSettings launchSettings) throws DebugException {
      super(launch);
      // Update references
      Assert.isNotNull(environment);
      Assert.isNotNull(environment.getBuilder());
      Assert.isNotNull(environment.getUi());
      Assert.isNotNull(launchSettings);
      this.launchSettings = launchSettings; 
      this.environment = environment;
      // Update initial model
      setModelIdentifier(MODEL_IDENTIFIER);
      Proof proof = environment.getBuilder().getProof();
      setName(proof.name() != null ? proof.name().toString() : "Unnamed");
      thread = new KeYThread(this, environment.getBuilder().getStartNode());
      registerDebugNode(thread);
      addSymbolicThread(thread);
      // Observe frozen state of KeY Main Frame
      environment.getBuilder().getMediator().addAutoModeListener(autoModeListener);
      // Initialize proof to use the symbolic execution strategy
      SymbolicExecutionEnvironment.configureProofForSymbolicExecution(environment.getBuilder().getProof(), KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun(), false, false, false);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return super.canResume() && 
             !environment.getBuilder().getMediator().autoMode() && // Only one proof completion per time is possible
             environment.getUi().isAutoModeSupported(environment.getBuilder().getProof()); // Otherwise Auto Mode is not available.
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
      Object element = KeySEDUtil.getSelectedDebugElement(); // To ask the UI for the selected element is a little bit ugly, but the only way because the Eclipse API does not provide the selected element.
      resume(element instanceof IKeYSEDDebugNode<?> ? (IKeYSEDDebugNode<?>)element : null);
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
         // Run auto mode
         runAutoMode(KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun(), 
                     keyNode != null ? SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()) : environment.getBuilder().getProof().openEnabledGoals(),
                     false,
                     false);
      }
   }
   
   /**
    * Runs the auto mode in KeY until the maximal number of set nodes are executed.
    * @param maximalNumberOfSetNodesToExecute The maximal number of set nodes to execute.
    * @param gaols The {@link Goal}s to work with.
    * @param stepOver Include step over stop condition?
    * @param stepReturn Include step return condition?
    */
   protected void runAutoMode(int maximalNumberOfSetNodesToExecute, 
                              ImmutableList<Goal> goals, 
                              boolean stepOver,
                              boolean stepReturn) {
      Proof proof = environment.getBuilder().getProof();
      // Set strategy to use
      StrategyProperties strategyProperties = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, true, isMethodTreatmentContract(proof), isLoopTreatmentInvariant(proof), isAliasChecks(proof));
      proof.setActiveStrategy(new SymbolicExecutionStrategy.Factory().create(proof, strategyProperties));
      // Update stop condition
      CompoundStopCondition stopCondition = new CompoundStopCondition();
      stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(maximalNumberOfSetNodesToExecute));
      if (stepOver) {
         stopCondition.addChildren(new StepOverSymbolicExecutionTreeNodesStopCondition());
      }
      if (stepReturn) {
         stopCondition.addChildren(new StepReturnSymbolicExecutionTreeNodesStopCondition());
      }
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      SymbolicExecutionUtil.updateStrategyPropertiesForSymbolicExecution(proof);
      environment.getUi().startAutoMode(proof, goals);
   }
   
   /**
    * Checks if the given {@link Proof} uses method treatment "Contract" right now.
    * @param proof The {@link Proof} to check.
    * @return {@code true} Contract, {@code false} Expand
    */
   protected boolean isMethodTreatmentContract(Proof proof) {
      StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      return StrategyProperties.METHOD_CONTRACT.equals(sp.getProperty(StrategyProperties.METHOD_OPTIONS_KEY));
   }
   
   /**
    * Checks if the given {@link Proof} uses loop treatment "Invariant" right now.
    * @param proof The {@link Proof} to check.
    * @return {@code true} Invariant, {@code false} Expand
    */
   protected boolean isLoopTreatmentInvariant(Proof proof) {
      StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      return StrategyProperties.LOOP_INVARIANT.equals(sp.getProperty(StrategyProperties.LOOP_OPTIONS_KEY));
   }
   
   /**
    * Checks if the given {@link Proof} uses alias checks right now.
    * @param proof The {@link Proof} to check.
    * @return {@code true} alias checks immediately, {@code false} alias checks never.
    */
   protected boolean isAliasChecks(Proof proof) {
      StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      return SymbolicExecutionStrategy.ALIAS_CHECK_IMMEDIATELY.equals(sp.getProperty(SymbolicExecutionStrategy.ALIAS_CHECK_OPTIONS_KEY));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return super.canSuspend() && 
             environment.getBuilder().getMediator().autoMode() && // Only if the auto mode is in progress
             environment.getBuilder().getMediator().getProof() == environment.getBuilder().getProof(); // And the auto mode handles this proof
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
      if (canSuspend()) {
         environment.getUi().stopAutoMode();
      }
   }
   
   /**
    * Suspends the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} to suspend.
    * @throws DebugException Occurred Exception.
    */
   public void suspend(IKeYSEDDebugNode<?> keyNode) throws DebugException {
      suspend();
   }

   /**
    * <p>
    * Updates the symbolic execution tree of the given {@link SymbolicExecutionTreeBuilder}
    * by calling {@link SymbolicExecutionTreeBuilder#analyse()}.
    * </p>
    * @param builder The {@link SymbolicExecutionTreeBuilder} to update.
    */
   protected void updateExecutionTree(SymbolicExecutionTreeBuilder builder) {
      // Update the symbolic execution tree, debug model is updated lazily via getters
      environment.getBuilder().analyse();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      if (!isTerminated()) {
         // Remove auto mode listener
         environment.getBuilder().getMediator().removeAutoModeListener(autoModeListener);
         // Suspend first to stop the automatic mode
         if (!isSuspended()) {
            suspend();
            environment.getUi().waitWhileAutoMode();
         }
         // Remove proof from user interface
         environment.getUi().removeProof(environment.getProof());
         // Clear cache
         environment.dispose();
         environment = null;
      }
      // Inform UI that the process is terminated
      super.terminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DebugException {
      // Remove auto mode listener
      environment.getBuilder().getMediator().removeAutoModeListener(autoModeListener);
      // Inform UI that the process is disconnected
      super.disconnect();
   }

   /**
    * When the auto mode is started.
    * @param e The event.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      if (e.getSource() == environment.getBuilder().getProof()) {
         try {
            // Inform UI that the process is resumed
            super.resume();
         }
         catch (DebugException exception) {
            LogUtil.getLogger().logError(exception);
         }
      }
   }

   /**
    * When the auto mode has stopped.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      if (e.getSource() == environment.getBuilder().getProof()) {
         try {
            updateExecutionTree(environment.getBuilder());
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
   }
   
   /**
    * Registers the given {@link IKeYSEDDebugNode} as child of this {@link KeYDebugTarget}.
    * @param node The {@link IKeYSEDDebugNode} to register as child.
    */
   public void registerDebugNode(IKeYSEDDebugNode<?> node) {
      if (node != null) {
         executionToDebugMapping.put(node.getExecutionNode(), node);
      }
   }
   
   /**
    * Returns the child {@link IKeYSEDDebugNode} for the given {@link IExecutionNode}.
    * @param executionNode The {@link IExecutionNode} for that the debug model representation is needed.
    * @return The found {@link IKeYSEDDebugNode} representation of the given {@link IExecutionNode} or {@code null} if no one is available.
    */
   public IKeYSEDDebugNode<?> getDebugNode(IExecutionNode executionNode) {
      return executionToDebugMapping.get(executionNode);
   }
   
   /**
    * Returns the used {@link KeYLaunchSettings}.
    * @return The used {@link KeYLaunchSettings}.
    */
   public KeYLaunchSettings getLaunchSettings() {
      return launchSettings;
   }

   /**
    * Checks if method return values are shown in {@link KeYMethodCall}s.
    * @return {@code true} include return value in node names, {@code false} do not show return values in node names.
    */
   public boolean isShowMethodReturnValuesInDebugNodes() {
      return launchSettings.isShowMethodReturnValues();
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
    * Executes the step into for the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step into.
    */
   public void stepInto(IKeYSEDDebugNode<?> keyNode) {
      runAutoMode(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_FOR_ONE_STEP, 
                  SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()),
                  false,
                  false);
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
    * Executes the step over for the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step over.
    */
   public void stepOver(IKeYSEDDebugNode<?> keyNode) {
      runAutoMode(KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun(), 
                  SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()),
                  true,
                  false);
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
    * Executes the step return for the given {@link IKeYSEDDebugNode}.
    * @param keyNode The {@link IKeYSEDDebugNode} which requests the step return.
    */
   public void stepReturn(IKeYSEDDebugNode<?> keyNode) {
      runAutoMode(KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun(), 
                  SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()),
                  false,
                  true);
   }
   
   /**
    * Returns the {@link Proof} instance from which the symbolic execution tree was extracted.
    * @return The {@link Proof} instance from which the symbolic execution tree was extracted.
    */
   public Proof getProof() {
      return environment != null ? environment.getProof() : null;
   }
   
   /**
    * Returns the {@link IMethod} which is debugged.
    * @return The debugged {@link IMethod}.
    */
   public IMethod getMethod() {
      return launchSettings.getMethod();
   }
}