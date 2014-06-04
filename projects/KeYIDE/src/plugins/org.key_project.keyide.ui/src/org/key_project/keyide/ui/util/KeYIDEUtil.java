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

package org.key_project.keyide.ui.util;

import java.io.File;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.common.ui.dialog.ContractSelectionDialog;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;
import org.key_project.key4eclipse.common.ui.util.EclipseUserInterfaceCustomization;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.editor.input.ProofOblInputEditorInput;
import org.key_project.keyide.ui.perspectives.KeYPerspective;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.nodeviews.TacletMenu;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Provides utility method for the KeYIDE.
 * @author Martin Hentschel
 */
public final class KeYIDEUtil {
   /**
    * Forbid instances.
    */
   private KeYIDEUtil() {
   }
   
   /**
    * Opens a dialog to select a contract for the specified method, furthermore creates the proof for that method
    * @param method The method to create the proof for.
    */
   public static void openProofEditor(final IMethod method) {
         try {
           if (method != null && method.exists()) {
               // Load location
               final IProject project = method.getResource().getProject();
               final File location = KeYUtil.getSourceLocation(project);
               final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
               final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
                 
               new Job("Loading Proof") { // A Job to load the proof in KeY
                  @Override
                    protected IStatus run(IProgressMonitor monitor) {
                       try {
                          SWTUtil.checkCanceled(monitor);
                          monitor.beginTask("Loading Proof Environment", IProgressMonitor.UNKNOWN);
                          final KeYEnvironment<CustomUserInterface> environment = KeYEnvironment.load(location, classPaths, bootClassPath, EclipseUserInterfaceCustomization.getInstance());
                          if (environment.getInitConfig() != null) {
                             // Get method to proof in KeY
                             final IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getJavaInfo());
                             if (pm != null) {
                                 KeYJavaType type = pm.getContainerType();
                                 final ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(type, pm);
                                 Runnable run = new Runnable() {
                                    @Override
                                    public void run() {
                                       try {
                                          // Open selection dialog
                                          Contract contract = openDialog(operationContracts, environment);
                                          if (contract != null) {
                                             KeYIDEUtil.openEditor(contract, environment, method);
                                          }
                                       }
                                       catch (Exception e) {
                                          LogUtil.getLogger().logError(e);
                                          LogUtil.getLogger().openErrorDialog(null, e);
                                       }  
                                    }
                                 };
                                 Display.getDefault().asyncExec(run);  
                             }
                             else {
                                return LogUtil.getLogger().createErrorStatus("Can't find method \"" + JDTUtil.getQualifiedMethodLabel(method) + "\" in KeY.");
                             }
                          }
                          return Status.OK_STATUS;                          
                       }
                       catch (OperationCanceledException e) {
                          return Status.CANCEL_STATUS;
                       }
                       catch (Exception e) {
                          LogUtil.getLogger().logError(e);
                          return LogUtil.getLogger().createErrorStatus(e);
                       }
                       finally {
                          monitor.done();
                       }
                  }
              }.schedule();
          }
       }
       catch (Exception e) {
          LogUtil.getLogger().logError(e);
       }
   }

   /**
    * Opens the currently selected {@link Proof} into the KeY-Editor.
    * @param contract The {@link Contract} to prove.
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    * @param method An optional {@link IMethod} from which the {@link Proof} was started.
    * @throws PartInitException Occurred Exception.
    */
   public static void openEditor(Contract contract, KeYEnvironment<?> environment, IMethod method)throws PartInitException{
      Assert.isNotNull(contract);
      Assert.isNotNull(environment);
      ProofOblInput problem = contract.createProofObl(environment.getInitConfig(), contract);
      IStorageEditorInput input = new ProofOblInputEditorInput(problem, environment, method);
      WorkbenchUtil.getActivePage().openEditor(input, KeYEditor.EDITOR_ID);
   }
   
   /**
    * Opens a dialog to select the {@link Contract} for the selected {@link IMethod}.
    * @param contracts - Set of available {@link Contract}s
    * @param environment - the given {@link KeYEnvironment}
    * @return the selected {@link Contract} or {@code null} if the dialog was cancelled.
    * @throws ProofInputException Occurred Exception
    */
   private static Contract openDialog(ImmutableSet<? extends Contract> contracts, KeYEnvironment<?> environment) throws ProofInputException {
      Assert.isNotNull(contracts);
      Assert.isNotNull(environment);
      Shell parent = WorkbenchUtil.getActiveShell();
      ImmutableCollectionContentProvider contentProvider = ImmutableCollectionContentProvider.getInstance();
      ContractSelectionDialog dialog = new ContractSelectionDialog(parent, contentProvider, environment.getServices());
      dialog.setTitle("Select Contract for Proof in KeY");
      dialog.setMessage("Select contract to prove.");
      dialog.setInput(contracts);
      
      if(!contracts.isEmpty()){
         dialog.setInitialSelections(new Contract[] {CollectionUtil.getFirst(contracts)});
      }
      if (dialog.open() == ContractSelectionDialog.OK) {
          Object result = dialog.getFirstResult();
          if (result instanceof Contract) {
              return (Contract)result;
          }
          else {
             throw new ProofInputException("The selected contract is no FunctionalOperationContract.");
          }
      }
      else {
         return null;
      }
   }

   /**
    * Asks the user if he wants to switch into the KeY-perspective and opens it if necessary
    */
   public static void switchPerspective() {
      if(KeYIDEUtil.shouldSwitchToKeyPerspective(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage())){
         WorkbenchUtil.openPerspective(KeYPerspective.PERSPECTIVE_ID);
      }
   }
   
   /**
    * Checks if a perspective switch to the state visualization perspective should be done.
    * @param activePage The currently active {@link IWorkbenchPage}.
    * @return {@code true} switch to state visualization perspective, {@code false} stay in current perspective.
    */
   public static boolean shouldSwitchToKeyPerspective(IWorkbenchPage activePage) {
      boolean switchPerspective = false;
      // Check if a different perspective is currently opened.
      if (!WorkbenchUtil.isPerspectiveOpen("org.key_project.keyide.ui.perspectives", activePage)) {
         String option = KeYIDEPreferences.getSwitchToKeyPerspective();
         if (MessageDialogWithToggle.ALWAYS.equals(option)) {
            switchPerspective = true;
         }
         else if (MessageDialogWithToggle.NEVER.equals(option)) {
            switchPerspective = false;
         }
         else {
            MessageDialogWithToggle dialog = MessageDialogWithToggle.openYesNoQuestion(activePage.getActivePart().getSite().getShell(), 
                                                                                       "Confirm Perspective Switch", 
                                                                                       "The Proof management is associated with the " + WorkbenchUtil.getPerspectiveName("org.key_project.keyide.ui.perspectives") + " perspective.\n\nDo you want to open this perspective now?", 
                                                                                       null, 
                                                                                       false, 
                                                                                       KeYIDEPreferences.getStore(), 
                                                                                       KeYIDEPreferences.SWITCH_TO_KEY_PERSPECTIVE);
            switchPerspective = (dialog.getReturnCode() == IDialogConstants.YES_ID);
         }
      }
      return switchPerspective;
   }

   /**
    * <p>
    * Collects all applicable {@link TacletApp}s for a given {@link PosInSequent} and {@link KeYMediator}.
    * </p>
    * <p>
    * The code behaves like the {@link TacletMenu}.
    * </p>
    * @param mediator - the {@link KeYMediator} of the current {@link Proof}.
    * @param pos - the {@link PosInSequent} to find the {@link TacletApp}s for.
    * @return {@link ImmutableList} - the {@link ImmutableList} with all applicable {@link TacletApp}s.
    */
   public static ImmutableList<TacletApp> findTaclets(KeYMediator mediator, PosInSequent pos) {
      if (pos != null) {
         ImmutableList<TacletApp> findList = mediator.getFindTaclet(pos);
         ImmutableList<TacletApp> rewriteList = mediator.getRewriteTaclet(pos);
         ImmutableList<TacletApp> noFindList = mediator.getNoFindTaclet();
         
         ImmutableList<TacletApp> find = TacletMenu.removeRewrites(findList).prepend(rewriteList);
         
         TacletMenu.TacletAppComparator comp = new TacletMenu.TacletAppComparator();
         ImmutableList<TacletApp> allTaclets = TacletMenu.sort(find, comp);
         
         if (pos != null && pos.isSequent()) {
            allTaclets = allTaclets.prepend(noFindList);
         }
         
         return allTaclets;
      }
      else{ 
         return null;
      }
   }
   
   /**
    * Collects all applicable {@link BuiltInRule}s.
    * @param mediator The {@link KeYMediator} of the current {@link Proof}.
    * @param pos The {@link PosInSequent} to find the {@link TacletApp}s for.
    * @return The {@link ImmutableList} with all applicable {@link BuiltInRule}s.
    */
   public static ImmutableList<BuiltInRule> findBuiltInRules(KeYMediator mediator, PosInSequent pos) {
      if (pos != null) {
         return mediator.getBuiltInRule(pos.getPosInOccurrence());
      }
      else {
         return ImmutableSLList.<BuiltInRule>nil();
      }
   }
}