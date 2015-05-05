package org.key_project.jmlediting.ui.preferencepages;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.key_project.javaeditor.preference.page.JavaExtensionsPreferencePage;
import org.key_project.javaeditor.preference.page.JavaExtensionsPreferencePage.EnabledState;
import org.key_project.javaeditor.preference.page.JavaExtensionsPreferencePage.ExtensionDescriptionState;
import org.key_project.javaeditor.util.ExtendableConfigurationUtil;
import org.key_project.javaeditor.util.ExtendableConfigurationUtil.ExtensionDescription;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;

/**
 * This class provides the top level entry for JML preferences in properties or
 * preference windows. Currently it does not contain anything.
 *
 * @author Moritz Lichter
 *
 */
@SuppressWarnings("restriction")
public class JMLPropertiesParentPage extends PropertyAndPreferencePage implements IWorkbenchPropertyPage {
   /**
    * Check box to enable if JML Editing should be enabled.
    */
   private Button enabledButton;
   
   /**
    * The by {@link #enabledButton} shown and edited {@link EnabledState}.
    */
   private EnabledState enabledState;
   
   /**
    * Listens for changes on an {@link EnabledState} of {@link #enabledState}.
    */
   private final PropertyChangeListener enabledStateListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleEnabledStatePropertyChange(evt);
      }
   };
   
   /**
    * The by {@link #enabledButton} shown and edited {@link ExtensionDescriptionState}.
    */
   private ExtensionDescriptionState jmlState;
   
   /**
    * Listens for changes on an {@link ExtensionDescriptionState} of {@link #extensionDescriptionStates}.
    */
   private final PropertyChangeListener jmlStateListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleJmlStatePropertyChange(evt);
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      JavaExtensionsPreferencePage.freeEnabledState(enabledState, getContainer(), enabledStateListener);
      JavaExtensionsPreferencePage.freeState(jmlState, getContainer(), jmlStateListener);
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(final Composite parent) {
      final Composite composite = new Composite(parent, SWT.NONE);
      composite.setLayout(new GridLayout(1, false));
      if (!this.isProjectPreferencePage()) {
         enabledState = JavaExtensionsPreferencePage.useEnabledSate(getContainer(), enabledStateListener);
         ExtensionDescription description = ExtendableConfigurationUtil.getExtensionDescription(JMLPreferencesHelper.JML_EDITOR_EXTENSION_ID);
         assert description != null;
         jmlState = JavaExtensionsPreferencePage.useState(description, getContainer(), jmlStateListener);
         
         this.enabledButton = new Button(composite, SWT.CHECK);
         this.enabledButton.setText("Enable JML Integration");
         this.enabledButton.setSelection(jmlState.isChecked() && enabledState.isChecked());
         this.enabledButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               handleJmlCheckboxSelected(e);
            }
         });
      }

      return composite;
   }

   /**
    * When the selection of {@link #enabledButton} has changed.
    * @param e The {@link SelectionEvent}.
    */
   protected void handleJmlCheckboxSelected(SelectionEvent e) {
      jmlState.setChecked(enabledButton.getSelection());
      if (enabledButton.getSelection()) {
         enabledState.setChecked(true);
      }
   }

   /**
    * When the checked state of {@link #jmlState} has changed.
    * @param evt The {@link PropertyChangeEvent}.
    */
   protected void handleJmlStatePropertyChange(PropertyChangeEvent evt) {
      enabledButton.setSelection(jmlState.isChecked() && enabledState.isChecked());
   }

   /**
    * When the checked state of {@link #enabledState} has changed.
    * @param evt The {@link PropertyChangeEvent}.
    */
   protected void handleEnabledStatePropertyChange(PropertyChangeEvent evt) {
      enabledButton.setSelection(jmlState.isChecked() && enabledState.isChecked());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Label createDescriptionLabel(final Composite parent) {
      final Label label = new Label(parent, SWT.NONE);
      return label;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createPreferenceContent(final Composite composite) {
      // Not used
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getPreferencePageID() {
      return "org.key_project.jmlediting.ui.preferences.jml";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getPropertyPageID() {
      return "org.key_project.jmlediting.ui.properties.jml";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performDefaults() {
      super.performDefaults();
      this.enabledState.setChecked(true);
      this.jmlState.setChecked(true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performApply() {
      this.update();
      super.performApply();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performOk() {
      return this.update() && super.performOk();
   }

   /**
    * Updates the preferences.
    *
    * @return true if the preferences was updated
    */
   private boolean update() {
      if (this.isProjectPreferencePage()) {
         return true;
      }
      else {
         PreferenceUtil.setExtensionsEnabled(enabledState.isChecked());
         PreferenceUtil.setExtensionEnabled(jmlState.getId(), jmlState.isChecked());
         return true;
      }
   }
}
