package org.key_project.sed.ui.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.ui.edit.ISEDAnnotationEditor;

/**
 * This {@link WizardPage} is used to edit an {@link ISEDAnnotation}.
 * @author Martin Hentschel
 */
public class EditWizardPage extends WizardPage {
   /**
    * The {@link ISEDAnnotation} to edit.
    */
   private final ISEDAnnotation annotation;
   
   /**
    * The optionally used {@link ISEDAnnotationEditor}.
    */
   private final ISEDAnnotationEditor editor;
   
   /**
    * Highlight background?
    */
   private Button highlightBackgroundButton;
   
   /**
    * Label in front of {@link #backgroundSelector}.
    */
   private Label backgroundLabel;

   /**
    * Selects the background color.
    */
   private ColorSelector backgroundSelector;

   /**
    * Highlight foreground?
    */
   private Button highlightForegroundButton;
   
   /**
    * Label in front of {@link #foregroundSelector}.
    */
   private Label foregroundLabel;
   
   /**
    * Selects the foreground color.
    */
   private ColorSelector foregroundSelector;
   
   /**
    * Restores the default values.
    */
   private Button restoreDefaultsButton;
   
   /**
    * Constructor.
    * @param pageName The name of this wizard page.
    * @param editor The optionally used {@link ISEDAnnotationEditor}.
    * @param annotation The {@link ISEDAnnotation} to edit.
    */
   public EditWizardPage(String pageName, ISEDAnnotationEditor editor, ISEDAnnotation annotation) {
      super(pageName);
      setTitle("Edit Annotation");
      setDescription("Change the details and the appearance of the annotation.");
      this.annotation = annotation;
      this.editor = editor;
      if (this.editor != null) {
         this.editor.addPropertyChangeListener(ISEDAnnotationEditor.PROP_ERROR_MESSAGE, new PropertyChangeListener() {
            @Override
            public void propertyChange(PropertyChangeEvent evt) {
               updatePageCompleted();
            }
         });
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      setControl(root);
      root.setLayout(new GridLayout(1, false));
      // Editor
      if (editor != null) {
         Control control = editor.createContent(root);
         if (control != null) {
            control.setLayoutData(new GridData(GridData.FILL_BOTH));
         }
      }
      // Appearance Group
      Group appearanceGroup = new Group(root, SWT.NONE);
      appearanceGroup.setText("Appearance");
      appearanceGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      appearanceGroup.setLayout(new GridLayout(2, false));
      // Background
      GridData highlightBackgroundButtonData = new GridData();
      highlightBackgroundButtonData.horizontalSpan = 2;
      highlightBackgroundButton = new Button(appearanceGroup, SWT.CHECK);
      highlightBackgroundButton.setLayoutData(highlightBackgroundButtonData);
      highlightBackgroundButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateBackgroundEnabled();
         }
      });
      backgroundLabel = new Label(appearanceGroup, SWT.NONE);
      backgroundLabel.setText("Background Color");
      highlightBackgroundButton.setText("Highlight Background Color");
      backgroundSelector = new ColorSelector(appearanceGroup);
      // Foreground
      GridData highlightForegroundButtonData = new GridData();
      highlightForegroundButtonData.horizontalSpan = 2;
      highlightForegroundButton = new Button(appearanceGroup, SWT.CHECK);
      highlightForegroundButton.setLayoutData(highlightForegroundButtonData);
      highlightForegroundButton.setText("Highlight Foreground Color");
      highlightForegroundButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateForegroundEnabled();
         }
      });
      foregroundLabel = new Label(appearanceGroup, SWT.NONE);
      foregroundLabel.setText("Foreground Color");
      foregroundSelector = new ColorSelector(appearanceGroup);
      // Defaults
      GridData restoreDefaultsButtonData = new GridData();
      restoreDefaultsButtonData.horizontalSpan = 2;
      restoreDefaultsButton = new Button(appearanceGroup, SWT.PUSH);
      restoreDefaultsButton.setLayoutData(restoreDefaultsButtonData);
      restoreDefaultsButton.setText("Restore Annotation &Defaults");
      restoreDefaultsButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            restoreDefaults();
            updateBackgroundEnabled();
            updateForegroundEnabled();
         }
      });
      // Update shown content
      updateShownContent();
      updateBackgroundEnabled();
      updateForegroundEnabled();
   }

   /**
    * Updates the shown content.
    */
   protected void updateShownContent() {
      highlightBackgroundButton.setSelection(annotation.isHighlightBackground());
      backgroundSelector.setColorValue(annotation.getBackgroundColor());
      highlightForegroundButton.setSelection(annotation.isHighlightForeground());
      foregroundSelector.setColorValue(annotation.getForegroundColor());
   }

   /**
    * Updates the enabled state of {@link #backgroundLabel} and {@link #backgroundSelector}.
    */
   protected void updateBackgroundEnabled() {
      boolean enabled = highlightBackgroundButton.getSelection();
      backgroundLabel.setEnabled(enabled);
      backgroundSelector.setEnabled(enabled);
   }
   
   /**
    * Updates the enabled state of {@link #foregroundLabel} and {@link #foregroundSelector}.
    */
   protected void updateForegroundEnabled() {
      boolean enabled = highlightForegroundButton.getSelection();
      foregroundLabel.setEnabled(enabled);
      foregroundSelector.setEnabled(enabled);
   }
   
   /**
    * Restores the default values.
    */
   protected void restoreDefaults() {
      ISEDAnnotationType type = annotation.getType();
      highlightBackgroundButton.setSelection(type.isHighlightBackground());
      backgroundSelector.setColorValue(type.getBackgroundColor());
      highlightForegroundButton.setSelection(type.isHighlightForeground());
      foregroundSelector.setColorValue(type.getForegroundColor());
   }
   
   /**
    * Updates the page completed state.
    */
   protected void updatePageCompleted() {
      if (editor != null) {
         String errorMessage = editor.getErrorMessage();
         setPageComplete(errorMessage == null);
         setErrorMessage(errorMessage);
      }
      else {
         setPageComplete(true);
         setErrorMessage(null);
      }
   }

   /**
    * Applies the changes to the {@link ISEDAnnotation}.
    */
   public void applyChanges() {
      ISEDAnnotationType type = annotation.getType();
      if (highlightBackgroundButton.getSelection() == type.isHighlightBackground()) {
         annotation.setCustomHighlightBackground(null);
      }
      else {
         annotation.setCustomHighlightBackground(highlightBackgroundButton.getSelection());
      }
      if (backgroundSelector.getColorValue().equals(type.getBackgroundColor())) {
         annotation.setCustomBackgroundColor(null);
      }
      else {
         annotation.setCustomBackgroundColor(backgroundSelector.getColorValue());
      }
      if (highlightForegroundButton.getSelection() == type.isHighlightForeground()) {
         annotation.setCustomHighlightForeground(null);
      }
      else {
         annotation.setCustomHighlightForeground(highlightForegroundButton.getSelection());
      }
      if (foregroundSelector.getColorValue().equals(type.getForegroundColor())) {
         annotation.setCustomForegroundColor(null);
      }
      else {
         annotation.setCustomForegroundColor(foregroundSelector.getColorValue());
      }
   }
}
