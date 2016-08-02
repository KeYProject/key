package org.key_project.sed.key.ui.slicing;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.slicing.AbstractKeYSlicer;
import org.key_project.sed.ui.slicing.SlicingSettingsControl;
import org.key_project.sed.ui.slicing.event.SlicingSettingsControlEvent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;

/**
 * Edits the settings of an {@link AbstractKeYSlicer}.
 * @author Martin Hentschel
 */
public class KeYSlicingSettingsControl extends SlicingSettingsControl {
   /**
    * {@link Combo} to select an equivalence class.
    */
   private final Combo combo;
   
   /**
    * The equivalence classes shown in {@link #combo}.
    */
   private List<ImmutableList<ISymbolicEquivalenceClass>> eqs;

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    */
   public KeYSlicingSettingsControl(Composite parent, int style) {
      super(parent, style);
      setLayout(new GridLayout(2, false));
      Label label = new Label(this, SWT.NONE);
      label.setText("&Equivalence Classes");
      combo = new Combo(this, SWT.READ_ONLY);
      combo.setLayoutData(new GridData(GridData.FILL_BOTH));
      combo.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            fireSettingsChanged(new SlicingSettingsControlEvent(KeYSlicingSettingsControl.this));
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(ISENode seedNode, ISEVariable seedVariable, IProgressMonitor monitor) throws DebugException {
      try {
         monitor.beginTask("Computing equivalence classes.", IProgressMonitor.UNKNOWN);
         // Check if parameters are valid.
         if (seedNode instanceof IKeYSENode<?>) {
            IKeYSENode<?> keyNode = (IKeYSENode<?>) seedNode;
            final List<ImmutableList<ISymbolicEquivalenceClass>> eqs = new ArrayList<ImmutableList<ISymbolicEquivalenceClass>>(keyNode.getExecutionNode().getLayoutsCount());
            for (int i = 0; i < keyNode.getExecutionNode().getLayoutsCount(); i++) {
               eqs.add(keyNode.getExecutionNode().getLayoutsEquivalenceClasses(i));
            }
            if (!eqs.isEmpty()) {
               getDisplay().syncExec(new Runnable() {
                  @Override
                  public void run() {
                     setEquivalenceClasses(eqs);
                  }
               });
            }
         }
      }
      catch (Exception e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
      finally {
         monitor.done();
      }
   }
   
   /**
    * Sets the available equivalence classes.
    * @param eqs The available equivalence classes.
    */
   protected void setEquivalenceClasses(List<ImmutableList<ISymbolicEquivalenceClass>> eqs) {
      combo.removeAll();
      this.eqs = eqs;
      if (eqs != null) {
         for (ImmutableList<ISymbolicEquivalenceClass> eq : eqs) {
            combo.add(ObjectUtil.toString(eq));
         }
         if (!eqs.isEmpty()) {
            combo.select(0);
            fireSettingsChanged(new SlicingSettingsControlEvent(this));
         }
      }
   }   

   /**
    * {@inheritDoc}
    */
   @Override
   public String validateSettings() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicEquivalenceClass> getSelectedSettings() {
      return getSelectedEquivalenceClass();
   }
   
   /**
    * Returns the selected equivalence class.
    * @return The selected equivalence class.
    */
   public ImmutableList<ISymbolicEquivalenceClass> getSelectedEquivalenceClass() {
      int index = combo.getSelectionIndex();
      if (eqs != null && index >= 0 && index < eqs.size()) {
         return eqs.get(index);
      }
      else {
         return null;
      }
   }
}
