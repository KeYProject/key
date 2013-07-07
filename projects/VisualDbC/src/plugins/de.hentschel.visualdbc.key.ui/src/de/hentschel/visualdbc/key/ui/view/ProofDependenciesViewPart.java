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

package de.hentschel.visualdbc.key.ui.view;

import java.util.LinkedHashSet;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderAdapter;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.job.ObjectchedulingRule;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.key.ui.editor.DbCModelDiagramEditor;
import de.hentschel.visualdbc.key.ui.editor.DbcModelEditorInput;
import de.hentschel.visualdbc.key.ui.editor.NothingActionBarContributor;
import de.hentschel.visualdbc.key.ui.util.LogUtil;
import de.hentschel.visualdbc.key.ui.util.ProofReferenceModelCreator;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * This {@link IViewPart} shows the dependencies of the {@link Proof} provided
 * by the active {@link IViewPart} if it provides an {@link IProofProvider} or
 * the active  {@link IEditorPart} otherwise as Visual DbC diagram. Only referenced
 * parts of the source code are shown.
 * @author Martin Hentschel
 */
public class ProofDependenciesViewPart extends AbstractEditorInViewView<DbCDiagramEditor, NothingActionBarContributor> {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "de.hentschel.visualdbc.key.ui.view.ProofDependenciesView";
   
   /**
    * Listens for changes on the {@link IWorkbenchPage} of this {@link IViewSite}.
    */
   private IPartListener partListener = new IPartListener() {
      @Override
      public void partOpened(IWorkbenchPart part) {
         handlePartOpened(part);
      }
      
      @Override
      public void partDeactivated(IWorkbenchPart part) {
         handlePartDeactivated(part);
      }
      
      @Override
      public void partClosed(IWorkbenchPart part) {
         handlePartClosed(part);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPart part) {
         handlePartBroughtToTop(part);
      }
      
      @Override
      public void partActivated(IWorkbenchPart part) {
         handlePartActivated(part);
      }
   };
   
   /**
    * A currently running {@link Job}.
    */
   private Job activeJob;
   
   /**
    * The currently observed {@link IWorkbenchPart} which is an {@link IViewPart} if it
    * provides an {@link IProofProvider} or the last active {@link IEditorPart} otherwise.
    */
   private IWorkbenchPart activeWorkbenchPart;

   /**
    * The currently observed {@link UserInterface} in which {@link #proof} lives.
    */
   private UserInterface userInterface;
   
   /**
    * The currently observed {@link Proof}s.
    */
   private Proof[] proofs;
   
   /**
    * The currently observed {@link IProofProvider} which provides {@link #proof} and {@link #userInterface}.
    */
   private IProofProvider proofProvider;

   /**
    * The listener which observes {@link #proofProvider}.
    */
   private IProofProviderListener proofProviderListener = new ProofProviderAdapter() {
      @Override
      public void currentProofsChanged(ProofProviderEvent e) {
         ProofDependenciesViewPart.this.proofsChanged();
      }
   }; 
   
   /**
    * The currently used {@link ProofReferenceModelCreator} which is updated
    * if a single rule is applied or replaced when the auto mode stopped/a prune was performed.
    */
   private ProofReferenceModelCreator creator;
   
   /**
    * {@link AutoModeListener} to observe auto mode start/stop events on {@link #environment}.
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         handleAutoModeStopped(e);
      }
      
      @Override
      public void autoModeStarted(ProofEvent e) {
         handleAutoModeStarted(e);
      }
   };

   /**
    * {@link ProofTreeListener} to observe changes on {@link #proof}.
    */
   private ProofTreeListener proofTreeListener = new ProofTreeListener() {
      @Override
      public void proofExpanded(ProofTreeEvent e) {
         handleProofChanged(e);
      }

      @Override
      public void proofIsBeingPruned(ProofTreeEvent e) {
      }

      @Override
      public void proofPruned(ProofTreeEvent e) {
         handleProofPruned(e);
      }

      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
         handleProofChanged(e);
      }

      @Override
      public void proofClosed(ProofTreeEvent e) {
         handleProofChanged(e);
      }

      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
      }

      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
      }

      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
      }

      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
         handleProofChanged(e);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      super.createPartControl(parent);
      getEditorPart().getDiagramEditPart().disableEditMode();
      getViewSite().getPage().addPartListener(partListener);
      activeWorkbenchPartChanged(searchActiveWorkbenchPart());
   }
   
   /**
    * Searches the active {@link IWorkbenchPart} to show.
    * @return The active {@link IWorkbenchPart} to show if available or {@code null} otherwise.
    */
   protected IWorkbenchPart searchActiveWorkbenchPart() {
      IWorkbenchPart activePart = WorkbenchUtil.getActivePart();
      if (shouldHandleWorkbenchPart(activePart)) {
         return activePart;
      }
      else {
         return WorkbenchUtil.getActiveEditor();
      }
   }
   
   /**
    * Checks if the given {@link IWorkbenchPart} should be treated or not.
    * @param part The {@link IWorkbenchPart} to check.
    * @return {@code true} treat it, {@code false} to not treat it.
    */
   protected boolean shouldHandleWorkbenchPart(IWorkbenchPart part) {
      if (part != this && part != null) {
         Object provider = part.getAdapter(IProofProvider.class);
         if (provider instanceof IProofProvider) {
            return true;
         }
         else {
            return part instanceof IEditorPart;
         }
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorInput createEditorInput() {
      return new DbcModelEditorInput(createEmptyModel());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected DbCDiagramEditor createEditorPart() {
      return new DbCModelDiagramEditor(false);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void initActionBars(IViewSite viewSite, IActionBars actionBars) {
      MenuManager fileMenu = new MenuManager("File", IWorkbenchActionConstants.M_FILE);
      actionBars.getMenuManager().add(fileMenu);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected NothingActionBarContributor createEditorActionBarContributor() {
      return new NothingActionBarContributor();
   }
   
   /**
    * Handles the event {@link IPartListener#partClosed(IWorkbenchPart)}.
    * @param part The closed {@link IWorkbenchPart}.
    */
   protected void handlePartClosed(IWorkbenchPart part) {
      if (activeWorkbenchPart == part) {
         activeWorkbenchPartChanged(searchActiveWorkbenchPart());
      }
   }

   /**
    * Handles the event {@link IPartListener#partOpened(IWorkbenchPart)}.
    * @param part The opened {@link IWorkbenchPart}.
    */
   protected void handlePartOpened(IWorkbenchPart part) {
      if (part != this) {
         activeWorkbenchPartChanged(searchActiveWorkbenchPart());
      }
   }

   /**
    * Handles the event {@link IPartListener#partActivated(IWorkbenchPart)}.
    * @param part The activated {@link IWorkbenchPart}.
    */
   protected void handlePartActivated(IWorkbenchPart part) {
      if (part != this) {
         activeWorkbenchPartChanged(searchActiveWorkbenchPart());
      }
   }

   /**
    * Handles the event {@link IPartListener#partBroughtToTop(IWorkbenchPart)}.
    * @param part The {@link IWorkbenchPart} brought to top.
    */
   protected void handlePartBroughtToTop(IWorkbenchPart part) {
   }

   /**
    * Handles the event {@link IPartListener#partDeactivated(IWorkbenchPart)}.
    * @param part The deactivated {@link IWorkbenchPart}.
    */
   protected void handlePartDeactivated(IWorkbenchPart part) {
   }
   
   /**
    * This method is called when the active editor has changed.
    * @param activeWorkbenchPart The new active editor.
    */
   protected void activeWorkbenchPartChanged(final IWorkbenchPart activeWorkbenchPart) {
      if (this.activeWorkbenchPart != activeWorkbenchPart) {
         this.activeWorkbenchPart = activeWorkbenchPart;
         // Remove old listeners
         if (proofProvider != null) {
            proofProvider.removeProofProviderListener(proofProviderListener);
         }
         // Request new proof provider
         if (activeWorkbenchPart != null) {
            proofProvider = (IProofProvider)activeWorkbenchPart.getAdapter(IProofProvider.class);
         }
         else {
            proofProvider = null;
         }
         // Add new listeners
         if (proofProvider != null) {
            proofProvider.addProofProviderListener(proofProviderListener);
         }
         // Update shown proof
         proofsChanged();
      }
   }

   /**
    * When the {@link Proof}s to show have changed.
    */
   protected void proofsChanged() {
      // Cancel existing job
      if (activeJob != null) {
         activeJob.cancel();
         activeJob = null;
      }
      // Remove old listener
      if (userInterface != null) {
         userInterface.getMediator().removeAutoModeListener(autoModeListener);
      }
      if (proofs != null) {
         for (Proof proof : proofs) {
            proof.removeProofTreeListener(proofTreeListener);
         }
      }
      //  Request new proof
      if (proofProvider != null) {
         userInterface = proofProvider.getUI();
         proofs = proofProvider.getCurrentProofs();
      }
      else {
         userInterface = null;
         proofs = null;
      }
      // Add new listeners
      if (userInterface != null && !ArrayUtil.isEmpty(proofs)) {
         userInterface.getMediator().addAutoModeListener(autoModeListener);
         for (Proof proof : proofs) {
            proof.addProofTreeListener(proofTreeListener);
         }
      }
      // Update shown content
      updateShownContent(null);
   }
   
   /**
    * Updates the shown content.
    * @param node Analyze references only of this {@link Node} or analyze the whole proof it is {@code null}.
    */
   protected void updateShownContent(final Node node) {
      if (userInterface != null && !ArrayUtil.isEmpty(proofs)) {
         activeJob = new Job("Visualizing Proof References") {
            @Override
            protected IStatus run(final IProgressMonitor monitor) {
               try {
                  // Analyze proof
                  monitor.beginTask("Analyzing proof", IProgressMonitor.UNKNOWN);
                  SWTUtil.checkCanceled(monitor);
                  LinkedHashSet<IProofReference<?>> references;
                  boolean updateRequired;
                  if (node != null) {
                     Services services = creator.getServices(node.proof());
                     if (services != null) {
                        references = ProofReferenceUtil.computeProofReferences(node, services);
                        updateRequired = !references.isEmpty();
                     }
                     else {
                        references = null;
                        updateRequired = false;
                     }
                  }
                  else {
                     references = new LinkedHashSet<IProofReference<?>>();
                     for (Proof proof : proofs) {
                        ProofReferenceUtil.merge(references, ProofReferenceUtil.computeProofReferences(proof));
                     }
                     creator = new ProofReferenceModelCreator(proofs);
                     updateRequired = true;
                  }
                  monitor.done();
                  // Create/Update model
                  if (updateRequired) {
                     SWTUtil.checkCanceled(monitor);
                     creator.updateModel(references, monitor);
                     // Change shown diagram
                     SWTUtil.checkCanceled(monitor);
                     final IEditorInput input = new DbcModelEditorInput(creator.getModel());
                     SWTUtil.checkCanceled(monitor);
                     if (!getEditorComposite().isDisposed()) {
                        IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
                           @Override
                           public void run() {
                              if (!monitor.isCanceled() && !getEditorComposite().isDisposed()) {
                                 getEditorPart().setInput(input);
                                 getEditorPart().getDiagramEditPart().disableEditMode();
                                 setMessage(null);
                                 setResult(Boolean.TRUE);
                              }
                           }
                        };
                        getEditorComposite().getDisplay().syncExec(run);
                        return run.getResult() != null && run.getResult().booleanValue() ? 
                               Status.OK_STATUS : 
                               Status.CANCEL_STATUS;
                     }
                     else {
                        return Status.CANCEL_STATUS;
                     }
                  }
                  else {
                     return Status.OK_STATUS;
                  }
               }
               catch (OperationCanceledException e) {
                  return Status.CANCEL_STATUS;
               }
               catch (Exception e) {
                  LogUtil.getLogger().logError(e);
                  return LogUtil.getLogger().createErrorStatus(e);
               }
            }
         };
         activeJob.setRule(new ObjectchedulingRule(this));
         activeJob.schedule();
      }
      else {
         setMessage("The active editor provides no supported proof.");
         getEditorPart().setInput(new DbcModelEditorInput(createEmptyModel()));
         getEditorPart().getDiagramEditPart().disableEditMode();
      }
   }
   
   /**
    * Creates an empty {@link DbcModel}. 
    * @return The empty {@link DbcModel}.
    */
   protected DbcModel createEmptyModel() {
      return DbcmodelFactory.eINSTANCE.createDbcModel();
   }

   /**
    * When the auto mode has started.
    * @param e The event.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      for (Proof proof : proofs) {
         proof.removeProofTreeListener(proofTreeListener);
      }
   }

   /**
    * When the auto mode has stopped.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      for (Proof proof : proofs) {
         proof.addProofTreeListener(proofTreeListener);
      }
      updateShownContent(null);
   }

   /**
    * When a prune was performed on the proof tree.
    * @param e The event.
    */
   protected void handleProofPruned(ProofTreeEvent e) {
      updateShownContent(null);
   }

   /**
    * When the proof tree has changed.
    * @param e The event.
    */
   protected void handleProofChanged(ProofTreeEvent e) {
      updateShownContent(e.getNode());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (proofProvider != null) {
         proofProvider.removeProofProviderListener(proofProviderListener);
      }
      if (userInterface != null) {
         userInterface.getMediator().removeAutoModeListener(autoModeListener);
      }
      if (proofs != null) {
         for (Proof proof : proofs) {
            proof.removeProofTreeListener(proofTreeListener);
         }
      }
      getViewSite().getPage().removePartListener(partListener);
      super.dispose();
   }

   /**
    * Returns the currently shown {@link DbcModel} or {@code null} if not available.
    * @return The currently shown {@link DbcModel} or {@code null} if not available.
    */
   public DbcModel getCurrentModel() {
      if (isMessageShown()) {
         return null;
      }
      else {
         return creator != null ? creator.getModel() : null;
      }
   }
}