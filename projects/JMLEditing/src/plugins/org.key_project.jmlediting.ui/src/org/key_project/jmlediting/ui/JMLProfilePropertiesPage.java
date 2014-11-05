package org.key_project.jmlediting.ui;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.key_project.jmlediting.core.IJMLProfile;
import org.key_project.jmlediting.core.JMLProfileManagement;

/**
 * The {@link JMLProfilePropertiesPage} implements a properties and preferences
 * page to show in project settings or global preferences. The page allows the
 * user to select a JML profile from available ones as project specific or
 * global default.
 * 
 * @author Moritz Lichter
 *
 */
public class JMLProfilePropertiesPage extends PropertyAndPreferencePage {

   /**
    * The ID of the page when acting as preference page.
    */
   public static final String JML_PROFILE_PREF_ID = "org.key_project.jmlediting.ui.preferences.profile";
   /**
    * The ID of the page when acting as properties page.
    */
   public static final String JML_PROFILE_PROP_ID = "org.key_project.jmlediting.ui.propertypages.profile";

   /**
    * The list which shows all profile names to the user.
    */
   private org.eclipse.swt.widgets.List profilesList;
   /**
    * The list of the profiles, in the same order as shown in the list.
    */
   private java.util.List<IJMLProfile> allProfiles;

   /**
    * The {@link IPreferenceChangeListener} which listens to changes of the
    * profile property for properties. This is used to change the selection in
    * the properies page when global settings are used and they change.
    */
   private IPreferenceChangeListener currentPreferenceListener;

   /**
    * Creates a new {@link JMLProfilePropertiesPage}.
    */
   public JMLProfilePropertiesPage() {
      this.currentPreferenceListener = new IPreferenceChangeListener() {

         @Override
         public void preferenceChange(final PreferenceChangeEvent event) {
            updateSelection();
         }
      };
   }

   @Override
   public void setVisible(boolean visible) {
      // Register the preference listener if the dialog is visible
      // do not generate memory leaks, listener are removed in
      // performOK and performCancel, here is too late
      if (visible) {
         IEclipsePreferences preferences = InstanceScope.INSTANCE
               .getNode(Activator.PLUGIN_ID);
         preferences
               .addPreferenceChangeListener(this.currentPreferenceListener);
      }
      super.setVisible(visible);
   }

   @Override
   protected Control createPreferenceContent(final Composite parent) {
      // Initialize the UI
      // Create a list for the profile with a label
      final Composite myComposite = new Composite(parent, SWT.NONE);

      final GridLayout layout = new GridLayout();
      layout.numColumns = 1;
      myComposite.setLayout(layout);

      GridData data;

      data = new GridData();
      Label label = new Label(myComposite, SWT.NONE);
      label.setText("Choose JML Profile from available ones:");
      label.setLayoutData(data);

      data = new GridData(GridData.FILL_BOTH);

      this.profilesList = new List(myComposite, SWT.V_SCROLL | SWT.SINGLE
            | SWT.BORDER);
      this.profilesList.setLayoutData(data);

      this.initUI();

      return myComposite;
   }

   /**
    * Initlializes the content of the UI. This method brings all available
    * profiles in the list and selects the current profile.
    */
   private void initUI() {
      // Get all profiles and set them to the list
      this.allProfiles = JMLProfileManagement
            .getAvailableProfilesSortedByName();
      for (IJMLProfile profile : this.allProfiles) {
         this.profilesList.add(profile.getName());
      }

      this.updateSelection();

      // Enable the list in preferences always and in project if project
      // specific settings are allowed
      this.setListEnabled(!this.isProjectPreferencePage()
            || this.useProjectSettings());
   }

   /**
    * Sets the list of profiles enabled or not.
    * 
    * @param enabled
    *           whether to enable the list or not
    */
   private void setListEnabled(boolean enabled) {
      this.profilesList.setEnabled(enabled);

      // Please dont ask me why I need this call here
      // But otherwise (at least on mac os) you can not reenable
      // the list, and, the list stays disables of setEnabled(false)
      // before
      this.profilesList.setEnabled(true);
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      // We have project specific options if a property is set on the project
      try {
         return project.getPersistentProperty(PropertyNames.PROFILE) != null;
      }
      catch (CoreException e) {
         return false;
      }
   }

   @Override
   protected void enableProjectSpecificSettings(
         boolean useProjectSpecificSettings) {
      if (!useProjectSpecificSettings) {
         // Reset selection to default if no project settings
         this.updateSelection();
      }
      this.setListEnabled(useProjectSpecificSettings);
      super.enableProjectSpecificSettings(useProjectSpecificSettings);
   }

   @Override
   protected String getPreferencePageID() {
      return JML_PROFILE_PREF_ID;
   }

   @Override
   protected String getPropertyPageID() {
      return JML_PROFILE_PROP_ID;
   }

   public static class DummyJMLProfile1 implements IJMLProfile {

      @Override
      public String getName() {
         return "DummyJMLProfile1";
      }

   }

   public static class DummyJMLProfile2 implements IJMLProfile {

      @Override
      public String getName() {
         return "DummyJMLProfile2";
      }

   }

   /**
    * Updates the selected profile in the list of profiles to match the profile
    * in the properties or preferences (with respect whether the pane is used
    * for preferences or properties).
    */
   private void updateSelection() {
      String currentProfileName = null;
      if (this.isProjectPreferencePage() || this.useProjectSettings()) {
         // Read local project properties if we are in a properties pane and
         // project specific settings are enabled
         try {
            currentProfileName = this.getProject().getPersistentProperty(
                  PropertyNames.PROFILE);
         }
         catch (CoreException e) {
            currentProfileName = null;
         }
      }
      // Read from global preferences if no project specific profile is set
      if (currentProfileName == null) {
         // Gobal preferences
         IEclipsePreferences preferences = InstanceScope.INSTANCE
               .getNode(Activator.PLUGIN_ID);
         currentProfileName = preferences.get(
               PropertyNames.DEFAULT_JML_PROFILE, null);

      }

      // Read the profile, if no profile found, use the first one if available
      IJMLProfile currentProfile = null;
      if (currentProfileName != null) {
         currentProfile = JMLProfileManagement
               .getProfileFromClassName(currentProfileName);
      }
      else if (this.allProfiles.size() > 0) {
         currentProfile = this.allProfiles.get(0);
      }
      // Select profile in the list
      this.profilesList.deselectAll();
      if (currentProfile != null) {
         int index = this.allProfiles.indexOf(currentProfile);
         if (index != -1) {
            this.profilesList.setSelection(index);
         }
         else {
            this.setErrorMessage("Profile \"" + currentProfile.getName()
                  + "\" is not available.");
         }
      }
      // Redraw the list because selection is otherwise not always cleared
      this.profilesList.redraw();
   }

   @Override
   public boolean performCancel() {
      // Remove preferences listener
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      preferences
            .removePreferenceChangeListener(this.currentPreferenceListener);
      return super.performCancel();
   }

   @Override
   public boolean performOk() {
      // Remove preference listener
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      preferences
            .removePreferenceChangeListener(this.currentPreferenceListener);

      String selectedProfileName = null;
      if (this.profilesList.getSelectionIndex() >= 0) {
         // Can only have one selection
         selectedProfileName = this.allProfiles
               .get(this.profilesList.getSelectionIndex()).getClass().getName();
      }

      // Only write into properties if a selection is available (user is forced
      // to)
      if (selectedProfileName == null) {
         return false;
      }

      if (this.isProjectPreferencePage()) {
         // Project preferences
         IProject project = this.getProject();
         try {
            if (this.useProjectSettings()) {
               // Set property
               project.setPersistentProperty(PropertyNames.PROFILE,
                     selectedProfileName);
            }
            else {
               // Remove property
               project.setPersistentProperty(PropertyNames.PROFILE, null);
            }
         }
         catch (CoreException e) {
            return false;
         }
      }
      else {
         // global properties
         preferences
               .put(PropertyNames.DEFAULT_JML_PROFILE, selectedProfileName);
      }

      return super.performOk();
   }

}
