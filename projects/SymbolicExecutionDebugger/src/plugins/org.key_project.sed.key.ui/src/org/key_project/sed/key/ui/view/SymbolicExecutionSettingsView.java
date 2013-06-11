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
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;
import org.key_project.util.java.CollectionUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * This view edits the proof search strategy settings in context of
 * symbolic execution debugging of the currently selected {@link Proof}
 * in view "Debug".
 * @author Martin Hentschel
 */
public class SymbolicExecutionSettingsView extends AbstractViewBasedView {
   /**
    * ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.key.ui.view.SymbolicExecutionProofSearchStragyView";

   /**
    * Shown string for method treatment "Expand".
    */
   public static final String METHOD_TREATMENT_EXPAND = "Expand";

   /**
    * Shown string for method treatment "Contract".
    */
   public static final String METHOD_TREATMENT_CONTRACT = "Contract";

   /**
    * Shown string for loop treatment "Expand".
    */
   public static final String LOOP_TREATMENT_EXPAND = "Expand";

   /**
    * Shown string for loop treatment "Invariant".
    */
   public static final String LOOP_TREATMENT_INVARIANT = "Invariant";

   /**
    * Shown string for alias check "Never".
    */
   public static final String ALIAS_CHECK_NEVER = "Never";

   /**
    * Shown string for alias check "Immediately".
    */
   public static final String ALIAS_CHECK_IMMEDIATELY = "Immediately";
   
   /**
    * Control to define the method treatment.
    */
   private Combo methodTreatmentCombo;

   /**
    * Control to define the loop treatment.
    */
   private Combo loopTreatmentCombo;

   /**
    * Control to define alias checks.
    */
   private Combo aliasChecksCombo;
   
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
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      // Initialize parent
      parent.setLayout(new GridLayout(1, false));
      // Method treatment
      Group methodTreatmentGroup = new Group(parent, SWT.NONE);
      methodTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      methodTreatmentGroup.setText("Method Treatment");
      methodTreatmentGroup.setLayout(new FillLayout());
      methodTreatmentCombo = new Combo(methodTreatmentGroup, SWT.READ_ONLY);
      methodTreatmentCombo.add(METHOD_TREATMENT_EXPAND);
      methodTreatmentCombo.add(METHOD_TREATMENT_CONTRACT);
      methodTreatmentCombo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateStrategySettings();
         }
      });
      // Loop treatment
      Group loopTreatmentGroup = new Group(parent, SWT.NONE);
      loopTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      loopTreatmentGroup.setText("Loop Treatment");
      loopTreatmentGroup.setLayout(new FillLayout());
      loopTreatmentCombo = new Combo(loopTreatmentGroup, SWT.READ_ONLY);
      loopTreatmentCombo.add(LOOP_TREATMENT_EXPAND);
      loopTreatmentCombo.add(LOOP_TREATMENT_INVARIANT);
      loopTreatmentCombo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateStrategySettings();
         }
      });
      // Alias checks
      Group aliasChecksGroup = new Group(parent, SWT.NONE);
      aliasChecksGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      aliasChecksGroup.setText("Alias Checks");
      aliasChecksGroup.setLayout(new FillLayout());
      aliasChecksCombo = new Combo(aliasChecksGroup, SWT.READ_ONLY);
      aliasChecksCombo.add(ALIAS_CHECK_NEVER);
      aliasChecksCombo.add(ALIAS_CHECK_IMMEDIATELY);
      aliasChecksCombo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateStrategySettings();
         }
      });
      // Set read-only if required
      updateShownValues();
   }

   /**
    * Updates the proof search strategy settings in the UI control when {@link #proof} has changed.
    */
   protected void updateShownValues() {
      setEditable(proof != null && !proof.isDisposed());
      if (proof != null && !proof.isDisposed()) {
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         showSettings(sp.getProperty(StrategyProperties.METHOD_OPTIONS_KEY), 
                      sp.getProperty(StrategyProperties.LOOP_OPTIONS_KEY),
                      sp.getProperty(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY));
      }
      else {
         showSettings(StrategyProperties.METHOD_EXPAND, 
                      StrategyProperties.LOOP_EXPAND,
                      StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER);
      }
   }

   /**
    * Makes UI controls editable or read-only.
    * @param editable {@code true} editable, {@code false} read-only.
    */
   protected void setEditable(boolean editable) {
      if (methodTreatmentCombo != null) {
         methodTreatmentCombo.setEnabled(editable);
      }
      if (loopTreatmentCombo != null) {
         loopTreatmentCombo.setEnabled(editable);
      }
      if (aliasChecksCombo != null) {
         aliasChecksCombo.setEnabled(editable);
      }
   }

   /**
    * Updates the shown proof search strategy settings.
    * @param methodOptionsKey The method treatment setting to show.
    * @param loopOptionsKey The loop treatment setting to show.
    * @param aliasCheckOptionsKey The alias treatment setting to show.
    */
   protected void showSettings(String methodOptionsKey, String loopOptionsKey, String aliasCheckOptionsKey) {
      if (methodTreatmentCombo != null) {
         methodTreatmentCombo.setText(StrategyProperties.METHOD_CONTRACT.equals(methodOptionsKey) ? METHOD_TREATMENT_CONTRACT : METHOD_TREATMENT_EXPAND);
      }
      if (loopTreatmentCombo != null) {
         loopTreatmentCombo.setText(StrategyProperties.LOOP_INVARIANT.equals(loopOptionsKey) ? LOOP_TREATMENT_INVARIANT : LOOP_TREATMENT_EXPAND);
      }
      if (aliasChecksCombo != null) {
         aliasChecksCombo.setText(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY.equals(aliasCheckOptionsKey) ? ALIAS_CHECK_IMMEDIATELY : ALIAS_CHECK_NEVER);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      methodTreatmentCombo.setFocus();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
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
            if (proof != null) {
               proofs.add(proof);
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
         proofChanged(CollectionUtil.getFirst(proofs));
      }
      else {
         // Make sure that the view does not listen for terminate events 
         if (debugEventListener != null) {
            DebugPlugin.getDefault().removeDebugEventListener(debugEventListener);
            debugEventListener = null;
         }
         // Update shown content
         proofsDebugTarget = null;
         CollectionUtil.getFirst(null);
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
                  // Update shown content and enabled state when the debug target was terminated
                  updateShownValues();
               }
            });
         }
      }
   }
   
   /**
    * When the proof, to manipulate its setting, has changed.
    * @param proof The new proof to manipulate proof search settings on it.
    */
   protected void proofChanged(Proof proof) {
      this.proof = proof;
      updateShownValues();
   }
   
   /**
    * Updates the {@link StrategyProperties} of {@link #proof} whe
    * a value has changed in the UI.
    */
   protected void updateStrategySettings() {
      boolean useOperationContracts = METHOD_TREATMENT_CONTRACT.equals(methodTreatmentCombo.getText());
      boolean useLoopInvariants = LOOP_TREATMENT_INVARIANT.equals(loopTreatmentCombo.getText());
      boolean aliasChecksImmediately = ALIAS_CHECK_IMMEDIATELY.equals(aliasChecksCombo.getText());
      SymbolicExecutionUtil.updateStrategySettings(proof, useOperationContracts, useLoopInvariants, aliasChecksImmediately);
   }
}