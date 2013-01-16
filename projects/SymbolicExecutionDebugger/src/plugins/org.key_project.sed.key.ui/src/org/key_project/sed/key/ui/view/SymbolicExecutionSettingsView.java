package org.key_project.sed.key.ui.view;

import java.util.HashSet;
import java.util.Set;

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
    * Control to define the method treatment.
    */
   private Combo methodTreatmentCombo;

   /**
    * The proof to edit its proof search strategy settings.
    */
   private Proof proof;
   
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
            methodTreatmentChanged(e);
         }
      });
      // Set read-only if required
      updateShownValues();
   }

   /**
    * Updates the proof search strategy settings in the UI control when {@link #proof} has changed.
    */
   protected void updateShownValues() {
      setEditable(proof != null);
      if (proof != null) {
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         showSettings(sp.getProperty(StrategyProperties.METHOD_OPTIONS_KEY));
      }
      else {
         showSettings(StrategyProperties.METHOD_EXPAND);
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
   }

   /**
    * Updates the shown proof search strategy settings.
    * @param methodOptionsKey The method treatment setting to show.
    */
   protected void showSettings(String methodOptionsKey) {
      if (methodTreatmentCombo != null) {
         methodTreatmentCombo.setText(StrategyProperties.METHOD_CONTRACT.equals(methodOptionsKey) ? METHOD_TREATMENT_CONTRACT : METHOD_TREATMENT_EXPAND);
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
            Proof proof = ((KeYDebugTarget) element).getProof();
            if (proof != null) {
               proofs.add(proof);
            }
         }
      }
      proofChanged(proofs.size() == 1 ? CollectionUtil.getFirst(proofs) : null);
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
    * When the selected method treatment has changed.
    * @param e The event.
    */
   protected void methodTreatmentChanged(SelectionEvent e) {
      SymbolicExecutionUtil.setUseOperationContracts(proof, METHOD_TREATMENT_CONTRACT.equals(methodTreatmentCombo.getText()));
   }
}
