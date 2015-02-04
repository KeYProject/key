package org.key_project.sed.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.key_project.sed.core.annotation.ISEDAnnotationAppearance;
import org.key_project.sed.core.annotation.impl.SliceAnnotationType;
import org.key_project.sed.core.slicing.ISEDSlicer;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.sed.ui.composite.AnnotationAppearanceComposite;
import org.key_project.sed.ui.util.SEDImages;

/**
 * This {@link WizardPage} defines search criteria.
 * @author Martin Hentschel
 */
public class SliceWizardPage extends WizardPage {
   /**
    * The available {@link ISEDSlicer}.
    */
   private final ISEDSlicer[] slicer;
   
   /**
    * The used {@link AnnotationAppearanceComposite}.
    */
   private AnnotationAppearanceComposite annotationAppearanceComposite;
   
   /**
    * {@link Combo} to select a slicing algorithm.
    */
   private Combo slicerCombo;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param slicer The available {@link ISEDSlicer}.
    */
   public SliceWizardPage(String pageName, ISEDSlicer[] slicer) {
      super(pageName);
      this.slicer = slicer;
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
      slicingGroup.setText("Slicing");
      slicingGroup.setLayout(new GridLayout(2, false));
      slicingGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      Label slicerLabel = new Label(slicingGroup, SWT.NONE);
      slicerLabel.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      slicerLabel.setText("&Algorithm");
      slicerCombo = new Combo(slicingGroup, SWT.BORDER | SWT.READ_ONLY);
      slicerCombo.setLayoutData(new GridData(GridData.FILL_BOTH));
      for (ISEDSlicer element : slicer) {
         slicerCombo.add(element.getName());
      }
      if (slicer.length >= 1) {
         slicerCombo.select(0);
      }
      slicerCombo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updatePageComplete();
         }
      });
      annotationAppearanceComposite = new AnnotationAppearanceComposite(root, SWT.NONE, SEDAnnotationUtil.getAnnotationtype(SliceAnnotationType.TYPE_ID));
      annotationAppearanceComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      updatePageComplete();
   }
   
   /**
    * Updates the page complete state.
    */
   protected void updatePageComplete() {
      if (getSlicer() == null) {
         setPageComplete(false);
         setErrorMessage("No slicing algorithm defined.");
      }
      else {
         setPageComplete(true);
         setErrorMessage(null);
      }
   }
   
   /**
    * Returns the selected {@link ISEDSlicer}.
    * @return The selected {@link ISEDSlicer}.
    */
   public ISEDSlicer getSlicer() {
      int index = slicerCombo.getSelectionIndex();
      return index >= 0 ? slicer[index] : null;
   }
   
   /**
    * Returns the specified {@link ISEDAnnotationAppearance}.
    * @return The specified {@link ISEDAnnotationAppearance}.
    */
   public ISEDAnnotationAppearance getAnnotationAppearance() {
      return annotationAppearanceComposite.getAnnotationAppearance();
   }
}
