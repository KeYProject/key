package org.key_project.sed.ui.wizard.page;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.key_project.sed.core.annotation.ISEAnnotationAppearance;
import org.key_project.sed.core.annotation.impl.SliceAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.sed.ui.composite.AnnotationAppearanceComposite;
import org.key_project.sed.ui.slicing.ISlicingSettingsControlFactory;
import org.key_project.sed.ui.slicing.SlicingSettingsControl;
import org.key_project.sed.ui.slicing.event.ISlicingSettingsControlListener;
import org.key_project.sed.ui.slicing.event.SlicingSettingsControlEvent;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.sed.ui.util.SlicingUtil;

/**
 * This {@link WizardPage} defines search criteria.
 * @author Martin Hentschel
 */
public class SliceWizardPage extends WizardPage {
   /**
    * The available {@link ISESlicer}.
    */
   private final ISESlicer[] slicer;
   
   /**
    * The seed {@link ISENode}.
    */
   private final ISENode seedNode;

   /**
    * The seed {@link IVariable}.
    */
   private final ISEVariable seedVariable;
   
   /**
    * The used {@link AnnotationAppearanceComposite}.
    */
   private AnnotationAppearanceComposite annotationAppearanceComposite;
   
   /**
    * {@link Combo} to select a slicing algorithm.
    */
   private Combo slicerCombo;
   
   /**
    * Contains the different slicing settings.
    */
   private Composite settingsRootComposite;
   
   /**
    * The {@link StackLayout} of {@link #settingsRootComposite}.
    */
   private StackLayout settingsRootCompositeLayout;
   
   /**
    * Maps each {@link ISESlicer} to its settings {@link Group}.
    */
   private final Map<ISESlicer, Group> settingsMap = new HashMap<ISESlicer, Group>();
   
   /**
    * Maps each {@link ISESlicer} to its control which edits the settings.
    */
   private final Map<ISESlicer, SlicingSettingsControl> settingsControlMap = new HashMap<ISESlicer, SlicingSettingsControl>();

   /**
    * Listens for changes on the {@link SlicingSettingsControl}s of {@link #settingsControlMap}.
    */
   private final ISlicingSettingsControlListener settingsListener = new ISlicingSettingsControlListener() {
      @Override
      public void settingsChanged(SlicingSettingsControlEvent e) {
         handleSettingsChanged(e);
      }
   };
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param slicer The available {@link ISESlicer}.
    * @param seedNode The seed {@link ISENode}.
    * @param seedVariable The seed {@link IVariable}.
    */
   public SliceWizardPage(String pageName, ISESlicer[] slicer, ISENode seedNode, ISEVariable seedVariable) {
      super(pageName);
      this.slicer = slicer;
      this.seedNode = seedNode;
      this.seedVariable = seedVariable;
      setTitle("Slicing");
      setDescription("Select the slicing algorithm.");
      setImageDescriptor(SEDImages.getImageDescriptor(SEDImages.SLICE_WIZARD));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      setControl(root);
      root.setLayout(new GridLayout(1, false));
      Group slicingGroup = new Group(root, SWT.NONE);
      slicingGroup.setText("Slicing Algorithm");
      slicingGroup.setLayout(new GridLayout(2, false));
      slicingGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      slicerCombo = new Combo(slicingGroup, SWT.BORDER | SWT.READ_ONLY);
      slicerCombo.setLayoutData(new GridData(GridData.FILL_BOTH));
      for (ISESlicer element : slicer) {
         slicerCombo.add(element.getName());
      }
      if (slicer.length >= 1) {
         slicerCombo.select(0);
      }
      slicerCombo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateSettings();
            updatePageComplete();
         }
      });
      settingsRootCompositeLayout = new StackLayout();
      settingsRootComposite = new Composite(root, SWT.NONE);
      settingsRootComposite.setLayout(settingsRootCompositeLayout);
      settingsRootComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      annotationAppearanceComposite = new AnnotationAppearanceComposite(root, SWT.NONE, SEAnnotationUtil.getAnnotationtype(SliceAnnotationType.TYPE_ID));
      annotationAppearanceComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      updateSettings();
      updatePageComplete();
   }

   /**
    * When the currently shown settings have changed.
    * @param e The {@link SlicingSettingsControlEvent}.
    */
   protected void handleSettingsChanged(SlicingSettingsControlEvent e) {
      updatePageComplete();
   }
   
   /**
    * Updates the shown settings.
    */
   protected void updateSettings() {
      final ISESlicer slicer = getSlicer();
      final ISlicingSettingsControlFactory factory = SlicingUtil.createSlicingSettingsControlFactory(slicer);
      if (slicer != null && factory != null) {
         Group group = settingsMap.get(slicer);
         if (group == null) {
            group = new Group(settingsRootComposite, SWT.NONE);
            group.setText("Settings");
            group.setLayout(new FillLayout());
            final SlicingSettingsControl control = factory.createControl(group);
            control.addSlicingSettingsControlListener(settingsListener);
            settingsControlMap.put(slicer, control);
            settingsMap.put(slicer, group);
            getContainer().getShell().getDisplay().asyncExec(new Runnable() {
               @Override
               public void run() {
                  try {
                     getContainer().run(true, false, new IRunnableWithProgress() {
                        @Override
                        public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
                           try {
                              control.init(seedNode, seedVariable, monitor);
                           }
                           catch (DebugException e) {
                              throw new InvocationTargetException(e);
                           }
                        }
                     });
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                     LogUtil.getLogger().openErrorDialog(getShell(), e);
                  }
               }
            });
         }
         settingsRootCompositeLayout.topControl = group;
      }
      else {
         settingsRootCompositeLayout.topControl = null;
      }
      settingsRootComposite.layout();
   }
   
   /**
    * Updates the page complete state.
    */
   protected void updatePageComplete() {
      ISESlicer slicer = getSlicer();
      if (slicer == null) {
         setPageComplete(false);
         setErrorMessage("No slicing algorithm defined.");
      }
      else {
         SlicingSettingsControl control = settingsControlMap.get(slicer);
         String settingsError = control != null ? control.validateSettings() : null;
         if (settingsError != null) {
            setPageComplete(false);
            setErrorMessage(settingsError);
         }
         else {
            setPageComplete(true);
            setErrorMessage(null);
         }
      }
   }
   
   /**
    * Returns the selected {@link ISESlicer}.
    * @return The selected {@link ISESlicer}.
    */
   public ISESlicer getSlicer() {
      int index = slicerCombo.getSelectionIndex();
      return index >= 0 ? slicer[index] : null;
   }
   
   /**
    * Returns the selected settings of the given {@link ISESlicer}.
    * @param slicer The {@link ISESlicer}.
    * @return The selected settings or {@code null} if not available.
    */
   public Object getSettings(ISESlicer slicer) {
      SlicingSettingsControl control = settingsControlMap.get(slicer);
      if (control != null) {
         return control.getSelectedSettings();
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the specified {@link ISEAnnotationAppearance}.
    * @return The specified {@link ISEAnnotationAppearance}.
    */
   public ISEAnnotationAppearance getAnnotationAppearance() {
      return annotationAppearanceComposite.getAnnotationAppearance();
   }
}
