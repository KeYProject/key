package org.key_project.sed.ui.composite;

import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationType;

/**
 * This {@link Composite} is used to edit the appearance of an {@link ISEDAnnotation}
 * @author Martin Hentschel
 */
public class AnnotationAppearanceComposite extends Composite {
   /**
    * The optional {@link ISEDAnnotationType} defining the default values.
    */
   private final ISEDAnnotationType annotationType;
   
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
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param annotation The optional {@link ISEDAnnotationType} defining the default values.
    */
   public AnnotationAppearanceComposite(Composite parent, int style, ISEDAnnotationType annotationType) {
      super(parent, style);
      this.annotationType = annotationType;
      setLayout(new FillLayout());
      // Appearance Group
      Group appearanceGroup = new Group(this, SWT.NONE);
      appearanceGroup.setText("Appearance");
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
      if (annotationType != null) {
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
      }
      // Update shown content
      showContent(annotationType);
      // Update enabled states.
      updateBackgroundEnabled();
      updateForegroundEnabled();
   }

   /**
    * Updates the shown content.
    */
   public void showContent(ISEDAnnotationType annotationType) {
      if (annotationType != null) {
         highlightBackgroundButton.setSelection(annotationType.isHighlightBackground());
         backgroundSelector.setColorValue(annotationType.getBackgroundColor());
         highlightForegroundButton.setSelection(annotationType.isHighlightForeground());
         foregroundSelector.setColorValue(annotationType.getForegroundColor());
      }
   }

   /**
    * Updates the shown content.
    */
   public void showContent(ISEDAnnotation annotation) {
      if (annotation != null) {
         highlightBackgroundButton.setSelection(annotation.isHighlightBackground());
         backgroundSelector.setColorValue(annotation.getBackgroundColor());
         highlightForegroundButton.setSelection(annotation.isHighlightForeground());
         foregroundSelector.setColorValue(annotation.getForegroundColor());
      }
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
      highlightBackgroundButton.setSelection(annotationType.isHighlightBackground());
      backgroundSelector.setColorValue(annotationType.getBackgroundColor());
      highlightForegroundButton.setSelection(annotationType.isHighlightForeground());
      foregroundSelector.setColorValue(annotationType.getForegroundColor());
   }

   /**
    * Applies the changes to the given {@link ISEDAnnotation}.
    * @param annotation The {@link ISEDAnnotation} to modify.
    */
   public void applyChanges(ISEDAnnotation annotation) {
      if (annotation != null) {
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
}
