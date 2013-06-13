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

import java.text.MessageFormat;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaExceptionBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;
import org.eclipse.jdt.internal.debug.ui.ConditionalBreakpointErrorDialog;
import org.eclipse.jdt.internal.debug.ui.DebugUIMessages;
import org.eclipse.jdt.internal.debug.ui.HotCodeReplaceErrorDialog;
import org.eclipse.jdt.internal.debug.ui.IJDIPreferencesConstants;
import org.eclipse.jdt.internal.debug.ui.JDIDebugUIPlugin;
import org.eclipse.jdt.internal.debug.ui.actions.JavaBreakpointPropertiesAction;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.key.core.launch.KeYLaunchSettings;
import org.key_project.sed.key.core.model.breakpoints.WatchPoint;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExceptionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.LineBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepOverSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepReturnSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.strategy.WatchpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Implementation if {@link ISEDDebugTarget} which uses KeY to symbolically
 * debug a program.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYDebugTarget extends SEDMemoryDebugTarget {
   
   /**
    * The {@link CompoundStopCondition} that holds all BreakpointsStopCOnditons for this {@link KeYDebugTarget}.
    */
   private CompoundStopCondition breakpointStopConditions = new CompoundStopCondition();
   
   /**
    * The Map of {@link JavaLineBreakpoint}s with their current HitCount as value.
    */
   private Map<IBreakpoint, IStopCondition> breakpointMap;
  
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
   
   private class ResourceChangeListener implements IResourceChangeListener{
      
      private KeYDebugTarget target;
      
      private IResourceDeltaVisitor visitor = new IResourceDeltaVisitor() {
         
         private boolean binFlag = false;
         
         @Override
         public boolean visit(IResourceDelta delta) throws CoreException {
            IResource resource = delta.getResource();
            if(resource!=null && IResource.FOLDER==resource.getType()&&resource.toString().contains("bin")){
               binFlag = true;
               return false;
            }
            if(resource!=null && IResource.FILE==resource.getType()&&resource.getFileExtension().equalsIgnoreCase("java")&&!binFlag){
               openHotCodeReplaceDialog(target);
               return false;
            }
            return true;
         }
      };
      
      public ResourceChangeListener(KeYDebugTarget target){
         this.target=target;
      }

      @Override
      public void resourceChanged(IResourceChangeEvent event) {
         try {
            event.getDelta().accept(visitor);
         }
         catch (CoreException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
      }
   }
   
   private IResourceChangeListener resourceListener = new ResourceChangeListener(this);

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
      breakpointMap = new HashMap<IBreakpoint, IStopCondition>();
      addBreakpoints();
      ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceListener, IResourceChangeEvent.POST_CHANGE);
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
      stopCondition.addChildren(breakpointStopConditions);
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
         environment.getBuilder().dispose();
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
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceListener);
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
   
   
   /**
    * Adds all Breakpoints to this DebugTarget. Is called only when the DebugTarget is initially created.
    */
   private void addBreakpoints(){      
      IBreakpoint[] breakpoints = DebugPlugin.getDefault().getBreakpointManager().getBreakpoints();      
      for(int i = 0; i < breakpoints.length; i++){
         breakpointAdded(breakpoints[i]);
         nothing();
      }
   }
   
   private int nothing(){
      return 5;
   }
   

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointAdded(IBreakpoint breakpoint) {
      try {
         if (breakpoint instanceof WatchPoint && !this.isTerminated()) {
            WatchPoint watchpoint = (WatchPoint) breakpoint;
            WatchpointStopCondition stopCondition = new WatchpointStopCondition(watchpoint.getHitCount(),
                  environment, environment.getBuilder().getProof(),
                  watchpoint.getCondition(), watchpoint.isEnabled());
            breakpointStopConditions.addChildren(stopCondition);
            breakpointMap.put(watchpoint, stopCondition);
         }
         else if (breakpoint instanceof JavaLineBreakpoint
               && !this.isTerminated()) {
            JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
            IResource resource = lineBreakpoint.getMarker().getResource();
            if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
               IMethod method = KeYUtil.getContainingMethod(lineBreakpoint.getLineNumber(), resource);
               IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getProof().getJavaInfo());
               int start = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset());
               int end = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
               LineBreakpointStopCondition stopCondition = new LineBreakpointStopCondition(
                     lineBreakpoint.getMarker().getResource().getLocation(),
                     lineBreakpoint.getLineNumber(),
                     lineBreakpoint.getHitCount(), environment, pm, environment
                           .getBuilder().getProof(), breakpointStopConditions,
                     lineBreakpoint.getCondition(), lineBreakpoint.isEnabled(),
                     lineBreakpoint.isConditionEnabled(), start, end);
               breakpointStopConditions.addChildren(stopCondition);
               breakpointMap.put(lineBreakpoint, stopCondition);
            }
         }
         else if (breakpoint instanceof JavaExceptionBreakpoint
               && !this.isTerminated()) {
            JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
            exceptionBreakpoint.isCaught();
            exceptionBreakpoint.isUncaught();
            exceptionBreakpoint.getHitCount();
            ExceptionBreakpointStopCondition stopCondition = new ExceptionBreakpointStopCondition(environment, exceptionBreakpoint.getTypeName());
            breakpointStopConditions.addChildren(stopCondition);
            breakpointMap.put(exceptionBreakpoint, stopCondition);
         }
      }
      catch (CoreException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      catch (ProofInputException e) {
         handleFailedToParse(e, breakpoint);
      }
      catch(TermCreationException e){
         handleFailedToParse(e, breakpoint);
      }
   }


   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointRemoved(IBreakpoint breakpoint, IMarkerDelta delta) {
      if(breakpoint instanceof WatchPoint){
         WatchPoint watchpoint = (WatchPoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(watchpoint));
         breakpointMap.remove(watchpoint);
      } else if(breakpoint instanceof JavaLineBreakpoint){
         JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(lineBreakpoint));
         breakpointMap.remove(lineBreakpoint);
      } else if(breakpoint instanceof JavaExceptionBreakpoint){
         JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(exceptionBreakpoint));
         breakpointMap.remove(exceptionBreakpoint);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointChanged(IBreakpoint breakpoint, IMarkerDelta delta) {
      try {
         if (breakpoint instanceof WatchPoint) {
            WatchPoint watchpoint = (WatchPoint) breakpoint;
            if (breakpointMap.containsKey(watchpoint)) {
               WatchpointStopCondition stopCondition = (WatchpointStopCondition) breakpointMap.get(watchpoint);
               stopCondition.setHitCount(watchpoint.getHitCount());
               stopCondition.setEnabled(watchpoint.isEnabled());
               stopCondition.setCondition(watchpoint.getCondition());
            }
            else {
               breakpointAdded(watchpoint);
            }
         }
         else if (breakpoint instanceof JavaLineBreakpoint) {
            JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
            if (breakpointMap.containsKey(lineBreakpoint)) {
               LineBreakpointStopCondition stopCondition = (LineBreakpointStopCondition) breakpointMap.get(lineBreakpoint);
               stopCondition.setHitCount(lineBreakpoint.getHitCount());
               stopCondition.setEnabled(lineBreakpoint.isEnabled());
               stopCondition.setConditionEnabled(lineBreakpoint.isConditionEnabled());
               stopCondition.setCondition(lineBreakpoint.getCondition());
            }
            else {
               breakpointAdded(lineBreakpoint);
            }
         }
         else if (breakpoint instanceof JavaExceptionBreakpoint) {
            JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
            if (breakpointMap.containsKey(exceptionBreakpoint)) {
               ExceptionBreakpointStopCondition stopCondition = (ExceptionBreakpointStopCondition) breakpointMap.get(exceptionBreakpoint);
               stopCondition.getClass();
            }
            else {
               breakpointAdded(exceptionBreakpoint);
            }
         }
      }
      catch (CoreException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      catch (ProofInputException e) {
         handleFailedToParse(e, breakpoint);
      }
      catch (TermCreationException e) {
         handleFailedToParse(e, breakpoint);
      }
   }

   private void openHotCodeReplaceDialog(final KeYDebugTarget target) {
      final Shell shell = WorkbenchUtil.getActiveShell();
      final IStatus status = new Status(IStatus.WARNING, JDIDebugUIPlugin.getUniqueIdentifier(), IStatus.WARNING, DebugUIMessages.JDIDebugUIPlugin_The_target_VM_does_not_support_hot_code_replace_1, null);
      final String preference= IJDIPreferencesConstants.PREF_ALERT_HCR_NOT_SUPPORTED;
      final String alertMessage= DebugUIMessages.JDIDebugUIPlugin_3; 
      final String title = DebugUIMessages.JDIDebugUIPlugin_Hot_code_replace_failed_1; 
      String vmName;
      try {
         vmName = target.getName();
      }
      catch (DebugException e) {
         vmName = DebugUITools.newDebugModelPresentation().getText(target);
      }
      ILaunchConfiguration config = target.getLaunch().getLaunchConfiguration();
      final String launchName = (config != null ? config.getName() : DebugUIMessages.JavaHotCodeReplaceListener_0);
      final String message = MessageFormat.format(DebugUIMessages.JDIDebugUIPlugin__0__was_unable_to_replace_the_running_code_with_the_code_in_the_workspace__2, new Object[] {vmName, launchName});
      
      Runnable run = new Runnable() {
         @Override
         public void run() {
            HotCodeReplaceErrorDialog dialog= new HotCodeReplaceErrorDialog(shell, title, message, status, preference, alertMessage, JDIDebugUIPlugin.getDefault().getPreferenceStore(), target);
            dialog.create();
            dialog.open();   
         }
      };
      Display.getDefault().asyncExec(run);   
   }

   private void handleFailedToParse(final Exception e, final IBreakpoint breakpoint) {
      Runnable run = new Runnable() {
         @Override
         public void run() {
            IStatus status= new Status(IStatus.ERROR, JDIDebugUIPlugin.getUniqueIdentifier(), IStatus.ERROR, e.getMessage(), null);
            ConditionalBreakpointErrorDialog dialog = new ConditionalBreakpointErrorDialog(WorkbenchUtil.getActiveShell(),"Condition could not be parsed to KeY.", status);
            dialog.create();
            int result = dialog.open();
            if (result == Window.OK) {
               JavaBreakpointPropertiesAction action= new JavaBreakpointPropertiesAction();
               action.selectionChanged(null, new StructuredSelection(breakpoint));
               action.run(null);
            }
            
         }
      };
      Display.getDefault().asyncExec(run);
   }   
  
}