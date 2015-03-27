package org.key_project.jmlediting.ui.preferencepages;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.NoSuchElementException;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.IProfileManagementListener;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceFactory;
import org.key_project.jmlediting.ui.Activator;
import org.key_project.jmlediting.ui.preferencepages.RebuildHelper.UserMessage;
import org.key_project.jmlediting.ui.preferencepages.profileDialog.JMLProfileDialog;
import org.key_project.util.eclipse.Logger;

/**
 * The {@link JMLProfilePropertiesPage} implements a properties and preferences
 * page to show in project settings or global preferences. The page allows the
 * user to select a JML profile from available ones as project specific or
 * global default.
 *
 * @author Moritz Lichter
 *
 */
@SuppressWarnings("restriction")
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
   private Table profilesListTable;
   /**
    * The list of the profiles, in the same order as shown in the list.
    */
   private java.util.List<IJMLProfile> allProfiles;

   /**
    * keep the difference between the selected (checked) Profile and the
    * selected (highlighted) profile to view/edit
    */
   private IJMLProfile profile2EditView;

   /**
    * The {@link IPreferenceChangeListener} which listens to changes of the
    * profile property for properties. This is used to change the selection in
    * the properies page when global settings are used and they change.
    */
   private IPreferenceChangeListener currentPreferenceListener;

   private IProfileManagementListener profileManagementListener;

   /**
    * needs to be global to change label-text
    */
   private Button editViewButton;
   private Button exportButton;
   private Button importButton;

   /**
    * Creates a new {@link JMLProfilePropertiesPage}.
    */
   public JMLProfilePropertiesPage() {
   }

   private void uninstallListener() {
      JMLPreferencesHelper
            .removeDefaultProfilePreferencesListener(this.currentPreferenceListener);
      JMLProfileManagement.instance().removeListener(
            this.profileManagementListener);
   }

   private void installListener() {
      this.currentPreferenceListener = JMLPreferencesHelper
            .buildDefaultProfilePreferencesListener(new IPreferenceChangeListener() {
               @Override
               public void preferenceChange(final PreferenceChangeEvent event) {
                  if (!JMLProfilePropertiesPage.this.profilesListTable
                        .isDisposed()) {
                     JMLProfilePropertiesPage.this.updateSelection();
                  }
               }
            });
      this.profileManagementListener = new IProfileManagementListener() {

         @Override
         public void newProfileAdded(final IJMLProfile newProfile) {
            JMLProfilePropertiesPage.this.fillTable();
         }
      };
      JMLProfileManagement.instance().addListener(
            this.profileManagementListener);
   }

   @Override
   public void setVisible(final boolean visible) {
      // Register the preference listener if the dialog is visible
      // do not generate memory leaks, listener are removed in
      // performOK and performCancel, here is too late
      if (visible) {
         this.installListener();
      }
      super.setVisible(visible);
   }

   @Override
   protected Control createPreferenceContent(final Composite parent) {
      // Initialize the UI
      // Create a list for the profile with a label
      final Composite myComposite = new Composite(parent, SWT.NONE);
      final GridLayout layout = new GridLayout();
      layout.numColumns = 2;
      myComposite.setLayout(layout);

      GridData data;

      data = new GridData();
      data.horizontalSpan = 2;
      final Label label = new Label(myComposite, SWT.NONE);
      label.setText("Choose active JML Profile from available ones:");
      label.setLayoutData(data);

      data = new GridData(SWT.FILL, SWT.TOP, true, true);
      data.horizontalSpan = 1;
      data.verticalSpan = 4;
      data.heightHint = 300;

      this.profilesListTable = new Table(myComposite, SWT.H_SCROLL
            | SWT.V_SCROLL | SWT.BORDER | SWT.CHECK | SWT.FULL_SELECTION);
      this.profilesListTable.setLayoutData(data);
      this.profilesListTable.setLinesVisible(true);
      this.profilesListTable.setHeaderVisible(true);

      this.initUI();

      final Button newButton = this
            .createTableSideButton(myComposite, "New...");
      this.editViewButton = this.createTableSideButton(myComposite, "Edit...");
      this.exportButton = this.createTableSideButton(myComposite, "Export...");
      this.importButton = this.createTableSideButton(myComposite, "Import...");

      this.updateSelection();

      this.exportButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {

            final IJMLProfile profile = JMLProfilePropertiesPage.this
                  .getSelectedProfile();
            if (!(profile instanceof IDerivedProfile)) {
               // Cannot occur because button is disabled, but prevent cast
               // exception altough
               return;
            }
            final FileDialog dialog = new FileDialog(
                  JMLProfilePropertiesPage.this.getShell(), SWT.SAVE);
            final String[] filterNames = new String[] { "XML File" };
            final String[] filterExtensions = new String[] { "*.xml" };
            dialog.setFilterNames(filterNames);
            dialog.setFilterExtensions(filterExtensions);
            final String file = dialog.open();
            if (file != null) {
               try {
                  final String xmlFileContent = ProfilePersistenceFactory
                        .createDerivedProfilePersistence().persist(
                              (IDerivedProfile) profile);
                  final FileWriter writer = new FileWriter(new File(file));
                  writer.write(xmlFileContent);
                  writer.flush();
                  writer.close();
               }
               catch (final ProfilePersistenceException e1) {
                  new Logger(Activator.getDefault(), Activator.PLUGIN_ID)
                        .logError(e1);
               }
               catch (final IOException e1) {
                  ErrorDialog.openError(JMLProfilePropertiesPage.this
                        .getShell(), "Failed to write the exported file",
                        "Due to an error: " + e1.getMessage(), new Status(
                              IStatus.ERROR, Activator.PLUGIN_ID,
                              "IO Exception", e1));
               }
            }
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      this.importButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            final FileDialog dialog = new FileDialog(
                  JMLProfilePropertiesPage.this.getShell(), SWT.OPEN);
            final String[] filterNames = new String[] { "XML File" };
            final String[] filterExtensions = new String[] { "*.xml" };
            dialog.setFilterNames(filterNames);
            dialog.setFilterExtensions(filterExtensions);
            final String file = dialog.open();
            if (file != null) {
               try {
                  final BufferedReader reader = new BufferedReader(
                        new FileReader(new File(file)));
                  String content = "";
                  String line;
                  while ((line = reader.readLine()) != null) {
                     content += line;
                  }
                  reader.close();
                  final IDerivedProfile profile = ProfilePersistenceFactory
                        .createDerivedProfilePersistence().read(content);
                  JMLProfileManagement.instance()
                        .addUserDefinedProfile(profile);

               }
               catch (final ProfilePersistenceException e1) {
                  ErrorDialog.openError(
                        JMLProfilePropertiesPage.this.getShell(),
                        "Failed to load the profile",
                        "The given profile cannot be loaded.",
                        new Status(IStatus.ERROR, Activator.PLUGIN_ID, e1
                              .getMessage(), e1));
               }
               catch (final IOException e1) {
                  ErrorDialog.openError(
                        JMLProfilePropertiesPage.this.getShell(),
                        "Failed to read the file",
                        "The selected file cannot be read to load the profile.",
                        new Status(IStatus.ERROR, Activator.PLUGIN_ID, e1
                              .getMessage(), e1));
               }
               catch (final InvalidProfileException e1) {
                  ErrorDialog.openError(
                        JMLProfilePropertiesPage.this.getShell(),
                        "Cannot import the profile",
                        "Failed to add the read profile to the list of available profiles in the workspace.",
                        new Status(IStatus.ERROR, Activator.PLUGIN_ID, e1
                              .getMessage(), e1));
               }
            }
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      newButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            final JMLProfileDialog dialog = new JMLProfileDialog(
                  JMLProfilePropertiesPage.this.getShell(), null);
            dialog.open();
            if (dialog.getReturnCode() == Window.OK) {
               JMLProfilePropertiesPage.this.fillTable();
            }
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      this.editViewButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            if (JMLProfilePropertiesPage.this.profile2EditView == null) {
               JMLProfilePropertiesPage.this.profile2EditView = JMLProfilePropertiesPage.this
                     .getCheckedProfile();
            }

            final JMLProfileDialog dialog = new JMLProfileDialog(
                  JMLProfilePropertiesPage.this.getShell(),
                  JMLProfilePropertiesPage.this.profile2EditView);
            dialog.open();
            // updates the table after closing editDialog with OK
            if (dialog.getReturnCode() == Window.OK) {
               JMLProfilePropertiesPage.this.fillTable();
            }
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });

      return myComposite;
   }

   private Button createTableSideButton(final Composite myComposite,
         final String name) {
      final Button button = new Button(myComposite, SWT.PUSH);
      button.setText(name);
      button.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false, 1, 1));

      return button;
   }

   /**
    * Initlializes the content of the UI. This method brings all available
    * profiles in the list and selects the current profile.
    */
   private void initUI() {
      final TableColumn nameColumn = new TableColumn(this.profilesListTable,
            SWT.LEFT);
      nameColumn.setMoveable(false);
      nameColumn.setWidth(175);
      nameColumn.setText("Profile Name");
      final TableColumn typeColumn = new TableColumn(this.profilesListTable,
            SWT.LEFT);
      typeColumn.setMoveable(false);
      typeColumn.setWidth(175);
      typeColumn.setText("Profile Type");
      this.fillTable();

      // Make sure that only one profile is available at a single time
      this.profilesListTable.addListener(SWT.Selection, new Listener() {
         @Override
         public void handleEvent(final Event event) {
            final TableItem item = (TableItem) event.item;
            final IJMLProfile profile = JMLProfilePropertiesPage.this
                  .getSelectedProfile();
            if (event.detail == SWT.CHECK) {
               if (item.getChecked()) {
                  for (final TableItem item2 : JMLProfilePropertiesPage.this.profilesListTable
                        .getItems()) {
                     if (item != item2) {
                        item2.setChecked(false);
                     }
                  }
                  JMLProfilePropertiesPage.this.setErrorMessage(null);
               }
               else {
                  boolean nothingChecked = true;
                  for (final TableItem item2 : JMLProfilePropertiesPage.this.profilesListTable
                        .getItems()) {
                     if (item2.getChecked()) {
                        nothingChecked = false;
                        break;
                     }
                  }
                  if (nothingChecked) {
                     JMLProfilePropertiesPage.this
                           .setErrorMessage("Please select an active profile");
                  }
               }

            }
            else {
               JMLProfilePropertiesPage.this.updateButtons(profile);
               JMLProfilePropertiesPage.this.profile2EditView = profile;
            }
         }

      });

   }

   private IJMLProfile getSelectedProfile() {
      return JMLProfilePropertiesPage.this.allProfiles
            .get(JMLProfilePropertiesPage.this.profilesListTable
                  .getSelectionIndex());
   }

   private void fillTable() {
      // Get all profiles and set them to the list
      this.allProfiles = JMLProfileManagement.instance()
            .getAvailableProfilesSortedByName();
      this.profilesListTable.removeAll();
      for (final IJMLProfile profile : this.allProfiles) {
         final TableItem item = new TableItem(this.profilesListTable, 0);
         final String type;
         if (this.isProfileDerived(profile)) {
            type = "derived from "
                  + ((IDerivedProfile) profile).getParentProfile().getName();
         }
         else {
            type = "standalone";
         }
         item.setText(new String[] { profile.getName(), type });
      }
      this.updateSelection();
   }

   private boolean isProfileDerived(final IJMLProfile profile) {
      return profile instanceof IDerivedProfile;
   }

   private void updateButtons(final IJMLProfile profile) {
      if (this.editViewButton == null) {
         return;
      }

      final boolean profileDerived = this.isProfileDerived(profile);
      if (profileDerived) {
         JMLProfilePropertiesPage.this.editViewButton.setText("Edit...");
      }
      else {
         JMLProfilePropertiesPage.this.editViewButton.setText("View...");
      }
      this.exportButton.setEnabled(profileDerived);
   }

   @Override
   protected void doStatusChanged() {
      // Enable the list in preferences always and in project if project
      // specific settings are allowed
      this.setListEnabled(!this.isProjectPreferencePage()
            || this.useProjectSettings());

      this.updateSelection();
   }

   /**
    * Sets the list of profiles enabled or not.
    *
    * @param enabled
    *           whether to enable the list or not
    */
   private void setListEnabled(final boolean enabled) {
      this.profilesListTable.setEnabled(enabled);
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      // We have project specific options if a property is set on the project
      return JMLPreferencesHelper.hasProjectJMLProfile(project);
   }

   @Override
   protected void enableProjectSpecificSettings(
         final boolean useProjectSpecificSettings) {
      super.enableProjectSpecificSettings(useProjectSpecificSettings);
      if (!useProjectSpecificSettings) {
         // Reset selection to default if no project settings
         this.updateSelection();
      }
      this.setListEnabled(useProjectSpecificSettings);
   }

   @Override
   protected String getPreferencePageID() {
      return JML_PROFILE_PREF_ID;
   }

   @Override
   protected String getPropertyPageID() {
      return JML_PROFILE_PROP_ID;
   }

   /**
    * Updates the selected profile in the list of profiles to match the profile
    * in the properties or preferences (with respect whether the pane is used
    * for preferences or properties).
    */
   private void updateSelection() {
      IJMLProfile currentProfile = null;
      if ((this.isProjectPreferencePage() && this.useProjectSettings())) {
         // Read local project properties if we are in a properties pane and
         // project specific settings are enabled
         currentProfile = JMLPreferencesHelper.getProjectJMLProfile(this
               .getProject());
      }
      // Read from global preferences if no project specific profile is set
      if (currentProfile == null) {
         // Gobal preferences
         try {
            currentProfile = JMLPreferencesHelper.getDefaultJMLProfile();
         }
         catch (final NoSuchElementException e) {
            this.setErrorMessage("No JML Profile available");
            return;
         }

         if (currentProfile == null) {
            this.setErrorMessage("Default JML Profile not available");
            return;
         }

      }
      assert currentProfile != null;
      // Select profile in the list
      for (final TableItem item : this.profilesListTable.getItems()) {
         item.setChecked(false);
      }
      final int index = this.allProfiles.indexOf(currentProfile);
      if (index != -1) {
         this.profilesListTable.getItem(index).setChecked(true);
      }
      else {

         this.setErrorMessage("Profile \"" + currentProfile.getName()
               + "\" is not available.");
      }

      this.updateButtons(currentProfile);

      // Redraw the list because selection is otherwise not always cleared
      this.profilesListTable.redraw();
   }

   @Override
   public boolean performCancel() {
      final boolean cancel = super.performCancel();
      if (cancel) {
         // Remove preferences listener
         this.uninstallListener();
      }
      return cancel;
   }

   private IJMLProfile getCurrentProfile() {
      if (this.isProjectPreferencePage()) {
         return JMLPreferencesHelper.getProjectActiveJMLProfile(this
               .getProject());
      }
      else {
         return JMLPreferencesHelper.getDefaultJMLProfile();
      }
   }

   private IJMLProfile getCheckedProfile() {
      for (int i = 0; i < this.profilesListTable.getItemCount(); i++) {
         // Can only have one selection
         if (this.profilesListTable.getItem(i).getChecked()) {
            final IJMLProfile result = this.allProfiles.get(i);
            return result;
         }
      }
      return null;
   }

   private boolean updatePreferences() {

      final IJMLProfile selectedProfile = this.getCheckedProfile();

      // Only write into properties if a selection is available (user is forced
      // to),
      if (selectedProfile == null && !this.useProjectSettings()) {

         return false;
      }

      // Create a runnable which applies to changes to the preferences
      final Runnable preferencesUpdater;
      Set<IProject> affectedProjects = null;

      // Check whether the affective profile has changed
      if (selectedProfile == this.getCurrentProfile()) {
         // Then we do not need to do a rebuild
         affectedProjects = Collections.emptySet();
      }

      if (this.isProjectPreferencePage()) {
         // Only write into properties if a selection is available (user
         // is forced
         // to)
         if (this.useProjectSettings() && selectedProfile == null) {
            return false;
         }
         // Project preferences
         final IProject project = this.getProject();
         // Check whether the effective profile for the project changed
         if (affectedProjects == null) {
            affectedProjects = Collections.singleton(project);
         }
         preferencesUpdater = new Runnable() {

            @Override
            public void run() {
               try {
                  if (JMLProfilePropertiesPage.this.useProjectSettings()) {
                     // Set property
                     JMLPreferencesHelper.setProjectJMLProfile(project,
                           selectedProfile);
                  }
                  else {
                     // Remove property
                     JMLPreferencesHelper.setProjectJMLProfile(project, null);
                  }

               }
               catch (final CoreException e) {
                  new Logger(Activator.getDefault(), Activator.PLUGIN_ID)
                        .logError("Failed to store preferences", e);
               }
            }
         };
      }
      else {
         if (affectedProjects == null) {
            affectedProjects = JMLProfileHelper
                  .getProjectsUsingWorkspaceProfile();
         }
         preferencesUpdater = new Runnable() {
            @Override
            public void run() {

               JMLPreferencesHelper

               .setDefaultJMLProfile(selectedProfile);
            }
         };
      }

      // Now trigger a rebuild for these projects and update the preferences
      return RebuildHelper.triggerRebuild(affectedProjects, this.getShell(),
            UserMessage.ACTIVE_PROFILE_CHANGED, preferencesUpdater);
   }

   @Override
   public void performApply() {
      this.updatePreferences();
   }

   @Override
   public boolean performOk() {
      final boolean ok = this.updatePreferences();
      if (ok) {
         // Window is closed, remove listener
         this.uninstallListener();
      }
      return ok;
   }
}
