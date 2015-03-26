package org.key_project.jmlediting.ui.preferencepages;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;

/**
 * This class provides the top level entry for JML preferences in properties or
 * preference windows. Currently it does not contain anything.
 *
 * @author Moritz Lichter
 *
 */
@SuppressWarnings("restriction")
public class JMLPropertiesParentPage extends PropertyAndPreferencePage
      implements IWorkbenchPropertyPage {

   /**
    * Checkbox to enable if JML Editing should be enabled.
    */
   private Button enableIntegrationCheckBox;

   /**
    * Creates a new instance.
    */
   public JMLPropertiesParentPage() {
   }

   @Override
   protected Control createContents(final Composite parent) {
      parent.setLayout(new GridLayout(1, false));
      final Composite wrapper = new Composite(parent, SWT.NONE);
      wrapper.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, true, true));
      wrapper.setLayout(new GridLayout(1, false));
      if (!this.isProjectPreferencePage()) {
         this.enableIntegrationCheckBox = new Button(wrapper, SWT.CHECK);
         this.enableIntegrationCheckBox.setText("Enable JML Integration");
         this.enableIntegrationCheckBox.setSelection(JMLPreferencesHelper
               .isExtensionEnabled());
         this.enableIntegrationCheckBox.setLayoutData(new GridData(SWT.LEFT,
               SWT.TOP, true, true));
      }

      return parent;
   }

   @Override
   protected Label createDescriptionLabel(final Composite parent) {
      final Label label = new Label(parent, SWT.NONE);
      return label;
   }

   @Override
   protected Control createPreferenceContent(final Composite composite) {
      // Not used
      return null;
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      return false;
   }

   @Override
   protected String getPreferencePageID() {
      return "org.key_project.jmlediting.ui.preferences.jml";
   }

   @Override
   protected String getPropertyPageID() {
      return "org.key_project.jmlediting.ui.properties.jml";
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
      final boolean isEnabledOld = JMLPreferencesHelper.isExtensionEnabled();
      final boolean isEnabled = this.enableIntegrationCheckBox.getSelection();
      if (isEnabledOld != isEnabled) {
         // Need a rebuild for all projects. Ask the user whether to do it now
         return RebuildHelper.triggerRebuild(null, this.getShell(),
               RebuildHelper.UserMessage.JML_EDITING_ON_OR_OFF, new Runnable() {

                  @Override
                  public void run() {
                     org.key_project.javaeditor.util.PreferenceUtil
                           .setExtensionEnabled(
                                 org.key_project.jmlediting.ui.Activator.EDITOR_EXTENSION_ID,
                                 isEnabled);
                     JMLPreferencesHelper.setExtensionEnabled(isEnabled);
                  }
               });
      }
      return true;
   }

   @Override
   protected void performDefaults() {
      super.performDefaults();
      this.enableIntegrationCheckBox.setSelection(true);
   }

   @Override
   protected void performApply() {
      this.update();
   }

   @Override
   public boolean performOk() {
      return this.update();
   }

}
