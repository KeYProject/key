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

package org.key_project.sed.key.ui.view;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.IDebugEventSetListener;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.key_project.key4eclipse.common.ui.composite.StrategySettingsComposite;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;
import org.key_project.util.java.CollectionUtil;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * This view edits the proof search strategy settings in context of
 * symbolic execution debugging of the currently selected {@link Proof}
 * in view "Debug".
 * @author Martin Hentschel
 */
public class SymbolicExecutionSettingsView extends AbstractViewBasedView implements IProofProvider {
   /**
    * ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.key.ui.view.SymbolicExecutionProofSearchStragyView";

   /**
    * Contains the registered {@link IProofProviderListener}.
    */
   private List<IProofProviderListener> proofProviderListener = new LinkedList<IProofProviderListener>();
   
   /**
    * The {@link KeYEnvironment} in which {@link #proof} lives.
    */
   private KeYEnvironment<?> environment;
   
   /**
    * The proof to edit its proof search strategy settings.
    */
   private Proof proof;
   
   /**
    * The {@link KeYDebugTarget} which provides {@link #proof}.
    */
   private KeYDebugTarget proofsDebugTarget;
   
   /**
    * Listens for selection changes on {@link #getBaseView()}.
    */
   private ISelectionChangedListener baseViewSelectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         SymbolicExecutionSettingsView.this.selectionChanged(event.getSelection());
      }
   };
   
   /**
    * Listens for debug events.
    */
   private IDebugEventSetListener debugEventListener;
   
   /**
    * Control used to edit the strategy settings.
    */
   private StrategySettingsComposite settingsComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      settingsComposite = new StrategySettingsComposite(parent, this, "No compatible debug target selected.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      if (settingsComposite != null && !settingsComposite.isDisposed()) {
         settingsComposite.setFocus();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (settingsComposite != null) {
         settingsComposite.dispose();
      }
      if (debugEventListener != null) {
         DebugPlugin.getDefault().removeDebugEventListener(debugEventListener);
         debugEventListener = null;
      }
      if (getBaseView() != null) {
         getBaseView().getSite().getSelectionProvider().removeSelectionChangedListener(baseViewSelectionListener);
      }
      super.dispose();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseViewReference(IViewReference baseViewReference) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(baseViewReference.getId());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseView(IViewPart baseView) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(baseView.getSite().getId());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView, IViewPart newBaseView) {
      if (oldBaseView != null) {
         oldBaseView.getSite().getSelectionProvider().removeSelectionChangedListener(baseViewSelectionListener);
      }
      if (newBaseView != null) {
         ISelectionProvider selectionProvider = newBaseView.getSite().getSelectionProvider();
         selectionProvider.addSelectionChangedListener(baseViewSelectionListener);
         selectionChanged(selectionProvider.getSelection());
      }
      else {
         selectionChanged(null);
      }
   }

   /**
    * When the selection on {@link #getBaseView()} has changed.
    * @param selection The new selection of {@link #getBaseView()}.
    */
   protected void selectionChanged(ISelection selection) {
      // Collect all selected proofs.
      Object[] elements = SWTUtil.toArray(selection);
      Set<Proof> proofs = new HashSet<Proof>();
      Set<KeYEnvironment<?>> environments = new HashSet<KeYEnvironment<?>>();
      KeYDebugTarget target = null;
      for (Object element : elements) {
         // Try to find the IDebugTarget
         if (element instanceof ILaunch) {
            element = ((ILaunch) element).getDebugTarget();
         }
         if (element instanceof IDebugElement) {
            element = ((IDebugElement) element).getDebugTarget();
         }
         // Check if the IDebugTarget provides a proof
         if (element instanceof KeYDebugTarget) {
            target = (KeYDebugTarget)element;
            Proof proof = target.getProof();
            if (proof != null && target.getEnvironment() != null) {
               proofs.add(proof);
               environments.add(target.getEnvironment());
            }
         }
      }
      if (proofs.size() == 1) {
         // Make sure that the view listens for terminate events
         if (debugEventListener == null) {
            debugEventListener = new IDebugEventSetListener() {
               @Override
               public void handleDebugEvents(DebugEvent[] events) {
                  for (DebugEvent event : events) {
                     handleDebugEvent(event);
                  }
               }
            };
            DebugPlugin.getDefault().addDebugEventListener(debugEventListener);
         }
         // Update shown content
         proofsDebugTarget = target;
         setProofAndEnvironment(CollectionUtil.getFirst(proofs), CollectionUtil.getFirst(environments));
      }
      else {
         // Make sure that the view does not listen for terminate events 
         if (debugEventListener != null) {
            DebugPlugin.getDefault().removeDebugEventListener(debugEventListener);
            debugEventListener = null;
         }
         // Update shown content
         proofsDebugTarget = null;
         setProofAndEnvironment(null, null);
      }
   }

   /**
    * When a debug event occurred.
    * @param event The event.
    */
   protected void handleDebugEvent(DebugEvent event) {
      if (event.getSource() == proofsDebugTarget) {
         if (event.getKind() == DebugEvent.TERMINATE) {
            getSite().getShell().getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  setProofAndEnvironment(null, null);
               }
            });
         }
      }
   }
   
   /**
    * Sets the currently provided {@link Proof} and its {@link KeYEnvironment}.
    * @param proof The {@link Proof} to set.
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    */
   protected void setProofAndEnvironment(Proof proof, KeYEnvironment<?> environment) {
      this.proof = proof;
      this.environment = environment;
      fireCurrentProofChanged(new ProofProviderEvent(this, getCurrentProofs(), getCurrentProof(), getUI(), getEnvironment()));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getCurrentProof() {
      return proof;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof[] getCurrentProofs() {
      return new Proof[] {proof};
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYEnvironment<?> getEnvironment() {
      return environment;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public UserInterface getUI() {
      return environment != null ? environment.getUi() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYMediator getMediator() {
      return environment != null ? environment.getMediator() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addProofProviderListener(IProofProviderListener l) {
      if (l != null) {
         proofProviderListener.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeProofProviderListener(IProofProviderListener l) {
      if (l != null) {
         proofProviderListener.remove(l);
      }
   }
   
   /**
    * Informs all registered {@link IProofProviderListener} about the event.
    * @param e The {@link ProofProviderEvent}.
    */
   protected void fireCurrentProofChanged(ProofProviderEvent e) {
      IProofProviderListener[] toInform = proofProviderListener.toArray(new IProofProviderListener[proofProviderListener.size()]);
      for (IProofProviderListener l : toInform) {
         l.currentProofChanged(e);
      }
   }
   
   /**
    * Informs all registered {@link IProofProviderListener} about the event.
    * @param e The {@link ProofProviderEvent}.
    */
   protected void fireCurrentProofsChanged(ProofProviderEvent e) {
      IProofProviderListener[] toInform = proofProviderListener.toArray(new IProofProviderListener[proofProviderListener.size()]);
      for (IProofProviderListener l : toInform) {
         l.currentProofsChanged(e);
      }
   }
}