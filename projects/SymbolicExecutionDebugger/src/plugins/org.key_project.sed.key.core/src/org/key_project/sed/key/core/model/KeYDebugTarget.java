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
import org.eclipse.jdt.debug.core.IJavaBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaExceptionBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaMethodBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaWatchpoint;
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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.impl.AbstractSEDDebugTarget;
import org.key_project.sed.key.core.breakpoints.KeYBreakpointManager;
import org.key_project.sed.key.core.breakpoints.KeYWatchpoint;
import org.key_project.sed.key.core.launch.KeYLaunchSettings;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.ProofUserManager;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

/**
 * Implementation if {@link ISEDDebugTarget} which uses KeY to symbolically
 * debug a program.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYDebugTarget extends AbstractSEDDebugTarget {
   /**
    * The {@link KeYBreakpointManager} that manages breakpoints for this target.
    */
   private final KeYBreakpointManager breakpointManager = new KeYBreakpointManager();
  
   /**
    * The used model identifier.
    */
   public static final String MODEL_IDENTIFIER = "org.key_project.sed.key.core";
   
   /**
    * The {@link KeYLaunchSettings} to use.
    */
   private final KeYLaunchSettings launchSettings;
   
   /**
    * The contained child threads.
    */
   private final KeYThread[] threads;
   
   /**
    * Listens for changed resources.
    */
   private final IResourceChangeListener resourceListener = new IResourceChangeListener() {
      @Override
      public void resourceChanged(IResourceChangeEvent event) {
         KeYDebugTarget.this.resourceChanged(event);
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
   private final Map<IExecutionNode<?>, IKeYSEDDebugNode<?>> executionToDebugMapping = new HashMap<IExecutionNode<?>, IKeYSEDDebugNode<?>>();
   
   /**
    * Observes the proof.
    */
   private final ProofDisposedListener proofDisposedListener = new ProofDisposedListener() {
      @Override
      public void proofDisposed(ProofDisposedEvent e) {
         handleProofDisposed(e);
      }
   };
   
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
      super(launch, true);
      DebugPlugin.getDefault().getBreakpointManager().addBreakpointListener(this);
      // Update references
      Assert.isNotNull(environment);
      Assert.isNotNull(environment.getBuilder());
      Assert.isNotNull(environment.getUi());
      Assert.isNotNull(launchSettings);
      this.launchSettings = launchSettings; 
      this.environment = environment;
      Proof proof = environment.getProof();
      proof.addProofDisposedListener(proofDisposedListener);
      ProofUserManager.getInstance().addUser(proof, environment, this);
      // Update initial model
      setModelIdentifier(MODEL_IDENTIFIER);
      setName(proof.name() != null ? proof.name().toString() : "Unnamed");
      // Init breakpoints
      initBreakpoints();
      // Add thread
      KeYThread thread = new KeYThread(this, environment.getBuilder().getStartNode());
      threads = new KeYThread[] {thread};
      // Initialize proof to use the symbolic execution strategy
      SymbolicExecutionEnvironment.configureProofForSymbolicExecution(environment.getBuilder().getProof(), KeYSEDPreferences.getMaximalNumberOfSetNodesPerBranchOnRun());
      ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceListener, IResourceChangeEvent.POST_CHANGE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYThread[] getSymbolicThreads() throws DebugException {
      return threads;
   }
   
   /**
    * Returns the used {@link KeYBreakpointManager}.
    * @return The used {@link KeYBreakpointManager}.
    */
   public KeYBreakpointManager getBreakpointManager() {
      return breakpointManager;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBreakpoint[] getBreakpoints() {
      return breakpointManager.getBreakpoints();
   }
   
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("unchecked")
   @Override
   protected boolean checkBreakpointHit(IBreakpoint breakpoint, ISEDDebugNode node) {
      if (node instanceof IKeYSEDDebugNode) {
         return breakpointManager.checkBreakpointHit(breakpoint, ((IKeYSEDDebugNode<IExecutionNode<?>>)node));
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      if (!isTerminated()) {
         // Remove Eclipse listeners
         ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceListener);
         DebugPlugin.getDefault().getBreakpointManager().removeBreakpointListener(this);
         // Suspend first to stop the automatic mode
         if (!isSuspended()) {
            suspend();
            environment.getUi().waitWhileAutoMode();
         }
         // Remove proof from user interface
         environment.getProof().removeProofDisposedListener(proofDisposedListener);
         ProofUserManager.getInstance().removeUserAndDispose(environment.getProof(), this);
         // Clear cache
         environment.dispose();
      }
      // Inform UI that the process is terminated
      super.terminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DebugException {
      environment.getProof().removeProofDisposedListener(proofDisposedListener);
      // Perform disconnect on threads
      for (KeYThread thread : threads) {
         thread.disconnect();
      }
      // Remove Eclipse listeners
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceListener);
      DebugPlugin.getDefault().getBreakpointManager().removeBreakpointListener(this);
      // Inform UI that the process is disconnected
      super.disconnect();
   }
   
   /**
    * Registers the given {@link IKeYSEDDebugNode} as child of this {@link KeYDebugTarget}.
    * @param node The {@link IKeYSEDDebugNode} to register as child.
    * @throws DebugException Occurred Exception
    */
   public void registerDebugNode(IKeYSEDDebugNode<?> node) throws DebugException {
      if (node != null) {
         IKeYSEDDebugNode<?> oldNode = executionToDebugMapping.put(node.getExecutionNode(), node);
         Assert.isTrue(oldNode == null);
         addToSourceModel(node);
      }
   }
   
   /**
    * Returns the child {@link IKeYSEDDebugNode} for the given {@link IExecutionNode}.
    * @param executionNode The {@link IExecutionNode} for that the debug model representation is needed.
    * @return The found {@link IKeYSEDDebugNode} representation of the given {@link IExecutionNode} or {@code null} if no one is available.
    */
   public IKeYSEDDebugNode<?> getDebugNode(IExecutionNode<?> executionNode) {
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
    * Checks if the signature is shown on {@link KeYMethodCall}s.
    * @return {@code true} show signature, {@code false} show only name.
    */
   public boolean isShowSignatureOnMethodReturnNodes() {
      return launchSettings.isShowSignatureOnMethodReturnNodes();
   }
   
   /**
    * Returns the {@link Proof} instance from which the symbolic execution tree was extracted.
    * @return The {@link Proof} instance from which the symbolic execution tree was extracted.
    */
   public Proof getProof() {
      return environment != null ? environment.getProof() : null;
   }
   
   /**
    * Returns the used {@link SymbolicExecutionEnvironment}.
    * @return The used {@link SymbolicExecutionEnvironment}.
    */
   public SymbolicExecutionEnvironment<?> getEnvironment() {
      return environment;
   }

   /**
    * Returns the {@link IMethod} which is debugged.
    * @return The debugged {@link IMethod}.
    */
   public IMethod getMethod() {
      return launchSettings.getMethod();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void initBreakpoint(IBreakpoint breakpoint) {
      breakpointAdded(breakpoint);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsBreakpoint(IBreakpoint breakpoint) {
      return breakpoint instanceof IJavaBreakpoint;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointAdded(IBreakpoint breakpoint) {
      try {
         if (breakpoint instanceof JavaWatchpoint
               && !this.isTerminated()) {
            JavaWatchpoint watchpoint = (JavaWatchpoint) breakpoint;
            breakpointManager.javaWatchpointAdded(watchpoint, environment);
         }
         else if (breakpoint instanceof JavaExceptionBreakpoint
               && !this.isTerminated()) {
            JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
            breakpointManager.exceptionBreakpointAdded(exceptionBreakpoint, environment);
         } 
         else if (breakpoint instanceof JavaMethodBreakpoint
               && !this.isTerminated()) {
            JavaMethodBreakpoint methodBreakpoint = (JavaMethodBreakpoint) breakpoint;
            breakpointManager.methodBreakpointAdded(methodBreakpoint, environment);
         }
         else if (breakpoint instanceof JavaLineBreakpoint
               && !this.isTerminated()) {
            JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
            breakpointManager.lineBreakpointAdded(lineBreakpoint, environment);
         }
         else if (breakpoint instanceof KeYWatchpoint
               && !this.isTerminated()) {
            KeYWatchpoint watchpoint = (KeYWatchpoint) breakpoint;
            breakpointManager.keyWatchpointAdded(watchpoint, environment);
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
      catch (ProofInputException e) {
         handleFailedToParse(e, breakpoint);
      }
      catch(TermCreationException e){
         handleFailedToParse(e, breakpoint);
      }
      finally {
         super.breakpointAdded(breakpoint);
      }
   }


   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointRemoved(IBreakpoint breakpoint, IMarkerDelta delta) {
      breakpointManager.breakpointRemoved(breakpoint, delta);
      super.breakpointRemoved(breakpoint, delta);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointChanged(IBreakpoint breakpoint, IMarkerDelta delta) {
      if(delta!=null&&!this.isDisconnected()){
         try {
            if (breakpoint instanceof JavaMethodBreakpoint) {
               JavaMethodBreakpoint methodBreakpoint = (JavaMethodBreakpoint) breakpoint;
               if (breakpointManager.getBreakpointMap().containsKey(methodBreakpoint)) {
                  breakpointManager.methodBreakpointChanged(methodBreakpoint);
               }
               else {
                  breakpointAdded(methodBreakpoint);
               }
            }
            else if (breakpoint instanceof JavaWatchpoint) {
               JavaWatchpoint javaWatchpoint = (JavaWatchpoint) breakpoint;
               if (breakpointManager.getBreakpointMap().containsKey(javaWatchpoint)) {
                  breakpointManager.javaWatchpointChanged(javaWatchpoint);
               }
               else {
                  breakpointAdded(javaWatchpoint);
               }
            }
            else if (breakpoint instanceof JavaLineBreakpoint) {
               JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
               if (breakpointManager.getBreakpointMap().containsKey(lineBreakpoint)) {
                  breakpointManager.javaLineBreakpointAdded(lineBreakpoint);
               }
               else {
                  breakpointAdded(lineBreakpoint);
               }
            }
            else if (breakpoint instanceof JavaExceptionBreakpoint) {
               JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
               if (breakpointManager.getBreakpointMap().containsKey(exceptionBreakpoint)) {
                  breakpointManager.exceptionBreakpointChanged(exceptionBreakpoint);
               }
               else {
                  breakpointAdded(exceptionBreakpoint);
               }
            }
            else if (breakpoint instanceof KeYWatchpoint) {
               KeYWatchpoint watchpoint = (KeYWatchpoint) breakpoint;
               if (breakpointManager.getBreakpointMap().containsKey(watchpoint)) {
                  breakpointManager.keyWatchpointChanged(watchpoint);
               }
               else {
                  breakpointAdded(watchpoint);
               }
            }
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
         catch (ProofInputException e) {
            handleFailedToParse(e, breakpoint);
         }
         catch (TermCreationException e) {
            handleFailedToParse(e, breakpoint);
         }
      }
      super.breakpointChanged(breakpoint, delta);
   }
 
   /**
    * Opens a dialog to tell the user that the hot code replace failed and gives options to handle that.
    * 
    * @param target the target on which the replace failed
    */
   protected void openHotCodeReplaceDialog() {
      if (!isTerminated() &&
          !isDisconnected() &&
          JDIDebugUIPlugin.getDefault().getPreferenceStore().getBoolean(IJDIPreferencesConstants.PREF_ALERT_HCR_NOT_SUPPORTED)) {
         final Shell shell = WorkbenchUtil.getActiveShell();
         final IStatus status = new Status(IStatus.WARNING, JDIDebugUIPlugin.getUniqueIdentifier(), IStatus.WARNING, "Cannot replace any code in running proof", null);
         final String preference= IJDIPreferencesConstants.PREF_ALERT_HCR_NOT_SUPPORTED;
         final String alertMessage= DebugUIMessages.JDIDebugUIPlugin_3; 
         final String title = DebugUIMessages.JDIDebugUIPlugin_Hot_code_replace_failed_1; 
         String vmName;
         try {
            vmName = getName();
         }
         catch (DebugException e) {
            vmName = DebugUITools.newDebugModelPresentation().getText(this);
         }
         ILaunchConfiguration config = getLaunch().getLaunchConfiguration();
         final String launchName = (config != null ? config.getName() : DebugUIMessages.JavaHotCodeReplaceListener_0);
         final String message =  "Code changes cannot be hot swapped into a running proof.\n\n" +
               "The current running proof ["+vmName+"] from launch ["+launchName+"] was unable to replace the running code with the code in the workspace.\n\n" +
               "It is safe to continue running the application, but you may notice discrepancies when debugging this application.";
         
         Runnable run = new Runnable() {
            @Override
            public void run() {
               HotCodeReplaceErrorDialog dialog = new HotCodeReplaceErrorDialog(shell, title, message, status, preference, alertMessage, JDIDebugUIPlugin.getDefault().getPreferenceStore(), KeYDebugTarget.this);
               dialog.setBlockOnOpen(true);
               dialog.create();
               dialog.open();
            }
         };
         Display.getDefault().asyncExec(run); 
      }  
   }

   /**
    * Opens a dialog when a condition could not be parsed by KeY and gives the option to correct it
    * 
    * @param e the Exception that caused the failure
    * @param breakpoint the breakpoint, for which the condition could not be parsed
    */
   protected void handleFailedToParse(final Exception e, final IBreakpoint breakpoint) {
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
               DebugPlugin.getDefault().getBreakpointManager().fireBreakpointChanged(breakpoint);
            }
            else{
               if(breakpoint instanceof JavaLineBreakpoint){
                  JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
                  try {
                     lineBreakpoint.setConditionEnabled(false);
                     lineBreakpoint.setCondition("");
                  }
                  catch (CoreException e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
            
         }
      };
      Display.getDefault().asyncExec(run);
   }

   /**
    * When the proof is disposed.
    * @param e The event.
    */
   protected void handleProofDisposed(ProofDisposedEvent e) {
      try {
         disconnect();
      }
      catch (DebugException exc) {
         LogUtil.getLogger().logError(exc);
      }
   }

   /**
    * Returns the {@link CompoundStopCondition} containing all {@link SymbolicExecutionBreakpointStopCondition}s of this target.
    * 
    * @return  the {@link CompoundStopCondition} containing all {@link SymbolicExecutionBreakpointStopCondition}s of this target
    */
   public SymbolicExecutionBreakpointStopCondition getBreakpointStopCondition() {
      return breakpointManager.getBreakpointStopCondition();
   } 
   
   /**
    * When an {@link IResource} has changed in the workspace.
    * @param event The {@link IResourceChangeEvent}.
    */
   public void resourceChanged(IResourceChangeEvent event) {
      try {
         ContainsRelevantJavaFileDeltaVisitor visitor = new ContainsRelevantJavaFileDeltaVisitor();
         IResourceDelta delta = event.getDelta();
         delta.accept(visitor);
         if (visitor.isContainsRelevantJavaFile()) {
            openHotCodeReplaceDialog();
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * Helper class used by {@link KeYDebugTarget#resourceChanged(IResourceChangeEvent)}.
    * @author Martin Hentschel
    */
   private class ContainsRelevantJavaFileDeltaVisitor implements IResourceDeltaVisitor {
      /**
       * The computed result.
       */
      private boolean containsRelevantJavaFile = false;

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean visit(IResourceDelta delta) throws CoreException {
         IResource resource = delta.getResource();
         if (resource != null && 
             delta.getFlags() != IResourceDelta.MARKERS &&
             JDTUtil.isJavaFile(resource)) {
            File location = ResourceUtil.getLocation(resource);
            if (location != null && 
                (IOUtil.contains(launchSettings.getLocation(), location) ||
                 IOUtil.contains(launchSettings.getClassPaths(), location) ||
                 IOUtil.contains(launchSettings.getBootClassPath(), location))) {
               containsRelevantJavaFile = true;
            }
         }
         return !containsRelevantJavaFile;
      }

      /**
       * Returns the computed result.
       * @return The computed result.
       */
      public boolean isContainsRelevantJavaFile() {
         return containsRelevantJavaFile;
      }
   }
}