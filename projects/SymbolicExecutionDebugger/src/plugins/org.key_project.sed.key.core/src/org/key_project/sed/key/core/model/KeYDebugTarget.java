package org.key_project.sed.key.core.model;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.core.util.LogUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
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
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
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
    * If this is {@code true} an {@link ISEDMethodReturn} will contain the return value,
    * but the performance will suffer.
    * If it is {@code false} only the name of the returned method is shown in an {@link ISEDMethodReturn}.
    */
   private boolean showMethodReturnValuesInDebugNodes;
   
   /**
    * The {@link SymbolicExecutionTreeBuilder} which is used to extract
    * the symbolic execution tree from KeY's proof tree.
    */
   private SymbolicExecutionTreeBuilder builder;

   /**
    * Maps an {@link IExecutionNode} to its representation in the debug model.
    */
   private Map<IExecutionNode, IKeYSEDDebugNode<?>> executionToDebugMapping = new HashMap<IExecutionNode, IKeYSEDDebugNode<?>>();
   
   /**
    * Constructor.
    * @param launch The parent {@link ILaunch}.
    * @param mediator the used {@link KeYMediator} during proof.
    * @param proof The {@link Proof} in KeY to treat.
    * @param showMethodReturnValuesInDebugNodes
    * @throws DebugException Occurred Exception
    */
   public KeYDebugTarget(ILaunch launch,
                         KeYMediator mediator,
                         Proof proof, 
                         boolean showMethodReturnValuesInDebugNodes) throws DebugException {
      super(launch);
      // Update references
      Assert.isNotNull(proof);
      this.builder = new SymbolicExecutionTreeBuilder(mediator, proof);
      this.showMethodReturnValuesInDebugNodes = showMethodReturnValuesInDebugNodes; 
      // Update initial model
      setModelIdentifier(MODEL_IDENTIFIER);
      setName(proof.name() != null ? proof.name().toString() : "Unnamed");
      thread = new KeYThread(this, builder.getStartNode());
      registerDebugNode(thread);
      addSymbolicThread(thread);
      // Observe frozen state of KeY Main Frame
      MainWindow.getInstance().getMediator().addAutoModeListener(autoModeListener);
      // Set goal chooser to use
      builder.getProof().getSettings().getStrategySettings().setCustomApplyStrategyGoalChooser(new SymbolicExecutionGoalChooser());
      // Set initial stop condition to use
      builder.getProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(new ExecutedSymbolicExecutionTreeNodesStopCondition(KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun()));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return super.canResume() && 
             !MainWindow.getInstance().frozen && // Only one proof completion per time is possible
             KeYUtil.isProofInUI(builder.getProof()); // Otherwise Auto Mode is not available.
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
                     keyNode != null ? SymbolicExecutionUtil.collectGoalsInSubtree(keyNode.getExecutionNode()) : builder.getProof().openEnabledGoals(),
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
      // Set strategy to use
      StrategyProperties strategyProperties = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, false, false, true);
      builder.getProof().setActiveStrategy(new SymbolicExecutionStrategy.Factory().create(builder.getProof(), strategyProperties));
      // Update stop condition
      CompoundStopCondition stopCondition = new CompoundStopCondition();
      stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(maximalNumberOfSetNodesToExecute));
      if (stepOver) {
         stopCondition.addChildren(new StepOverSymbolicExecutionTreeNodesStopCondition());
      }
      if (stepReturn) {
         stopCondition.addChildren(new StepReturnSymbolicExecutionTreeNodesStopCondition());
      }
      builder.getProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      KeYUtil.runProofInAutomaticModeWithoutResultDialog(builder.getProof(), goals);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return super.canSuspend() && 
             MainWindow.getInstance().frozen && // Only if the auto mode is in progress
             MainWindow.getInstance().getMediator().getProof() == builder.getProof(); // And the auto mode handles this proof
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
         MainWindow.getInstance().getMediator().stopAutoMode();
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
      builder.analyse();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      // Remove auto mode listener
      MainWindow main = MainWindow.getInstance(); 
      main.getMediator().removeAutoModeListener(autoModeListener);
      // Suspend first to stop the automatic mode
      if (!isSuspended()) {
         suspend();
         KeYUtil.waitWhileMainWindowIsFrozen(main);
      }
      // Remove proof from user interface
      KeYUtil.removeFromProofList(main, builder.getProof().env());
      // Clear cache
      builder.dispose();
      builder = null;
      executionToDebugMapping.clear();
      // Inform UI that the process is terminated
      super.terminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DebugException {
      // Remove auto mode listener
      MainWindow.getInstance().getMediator().removeAutoModeListener(autoModeListener);
      // Inform UI that the process is disconnected
      super.disconnect();
   }

   /**
    * When the auto mode is started.
    * @param e The event.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      try {
         if (e.getSource() == builder.getProof()) {
            // Inform UI that the process is resumed
            super.resume();
         }
      }
      catch (DebugException exception) {
         LogUtil.getLogger().logError(exception);
      }
   }

   /**
    * When the auto mode has stopped.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      try {
         if (e.getSource() == builder.getProof()) {
            updateExecutionTree(builder);
         }
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
    * Checks if method return values are shown in {@link KeYMethodCall}s.
    * @return {@code true} include return value in node names, {@code false} do not show return values in node names.
    */
   public boolean isShowMethodReturnValuesInDebugNodes() {
      return showMethodReturnValuesInDebugNodes;
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
}
