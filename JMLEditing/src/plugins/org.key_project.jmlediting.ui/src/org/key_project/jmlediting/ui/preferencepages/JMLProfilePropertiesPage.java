package org.key_project.jmlediting.ui.preferencepages;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ICheckStateProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.key_project.javaeditor.util.LogUtil;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceFactory;
import org.key_project.jmlediting.ui.Activator;
import org.key_project.jmlediting.ui.preferencepages.RebuildHelper.UserMessage;
import org.key_project.jmlediting.ui.provider.JMLProfileLabelProvider;
import org.key_project.jmlediting.ui.wizard.JMLProfileWizard;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * The {@link JMLProfilePropertiesPage} implements a properties and preferences
 * page to show in project settings or global preferences. The page allows the
 * user to select a JML profile from available ones as project specific or
 * global default.
 *
 * @author Moritz Lichter
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
   public static final String JML_PROFILE_PROP_ID = "org.key_project.jmlediting.ui.properties.profile";

   /**
    * The list which shows all profile names to the user.
    */
   private CheckboxTableViewer profilesViewer;

   private IJMLProfile checkedProfile;

   /**
    * needs to be global to change label-text.
    */
   private Button editViewButton;
   private Button exportButton;
   private Button importButton;
   private Button deleteButton;

   @Override
   protected Control createPreferenceContent(final Composite parent) {
      // Compute initially checked profile
      checkedProfile = getCurrentProfile();
      // Initialize the UI
      // Create a list for the profile with a label
      final Composite myComposite = new Composite(parent, SWT.NONE);
      final GridLayout layout = new GridLayout();
      layout.numColumns = 2;
      myComposite.setLayout(layout);

      GridData data = new GridData();
      data.horizontalSpan = 2;
      final Label label = new Label(myComposite, SWT.NONE);
      label.setText("Choose active JML Profile from available ones:");
      label.setLayoutData(data);

      data = new GridData(SWT.FILL, SWT.TOP, true, true);
      data.horizontalSpan = 1;
      data.verticalSpan = 5;
      data.heightHint = 300;

      Composite tableComposite = new Composite(myComposite, SWT.NONE);
      tableComposite.setLayoutData(data);
      TableColumnLayout tableLayout = new TableColumnLayout();
      tableComposite.setLayout(tableLayout);
      
      this.profilesViewer = CheckboxTableViewer.newCheckList(tableComposite, SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION);
      this.profilesViewer.getTable().setLinesVisible(true);
      this.profilesViewer.getTable().setHeaderVisible(true);

      final TableViewerColumn nameColumn = new TableViewerColumn(this.profilesViewer, SWT.LEFT);
      nameColumn.getColumn().setMoveable(false);
      nameColumn.getColumn().setText("Profile Name");
      tableLayout.setColumnData(nameColumn.getColumn(), new ColumnWeightData(50));
      final TableViewerColumn typeColumn = new TableViewerColumn(this.profilesViewer, SWT.LEFT);
      typeColumn.getColumn().setMoveable(false);
      typeColumn.getColumn().setText("Profile Type");
      tableLayout.setColumnData(typeColumn.getColumn(), new ColumnWeightData(50));
      
      profilesViewer.setContentProvider(ArrayContentProvider.getInstance());
      profilesViewer.setLabelProvider(new JMLProfileLabelProvider());
      profilesViewer.setCheckStateProvider(new ICheckStateProvider() {
         @Override
         public boolean isChecked(Object element) {
            return ObjectUtil.equals(checkedProfile, element);
         }
         
         @Override
         public boolean isGrayed(Object element) {
            return false;
         }
      });
      updateProfileViewer();
      profilesViewer.addCheckStateListener(new ICheckStateListener() {
         @Override
         public void checkStateChanged(CheckStateChangedEvent event) {
            handleProfileCheckStateChanged(event);
         }
      });
      profilesViewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            handleProfileSelectionChanged(event);
         }
      });

      final Button newButton = this.createTableSideButton(myComposite, "New...");
      this.editViewButton = this.createTableSideButton(myComposite, "Edit...");
      this.deleteButton = this.createTableSideButton(myComposite, "Delete");
      this.exportButton = this.createTableSideButton(myComposite, "Export...");
      this.importButton = this.createTableSideButton(myComposite, "Import...");

      this.exportButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            exportProfile();
         }
      });
      this.importButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            importProfile();
         }
      });
      this.deleteButton.addSelectionListener(new SelectionAdapter() {

         @Override
         public void widgetSelected(final SelectionEvent e) {
            deleteProfile();
         }
      });
      newButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            createNewProfile();
         }
      });
      this.editViewButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            editProfile();
         }
      });
      updateButtonsEnabledState();
      return myComposite;
   }

   protected void handleProfileCheckStateChanged(CheckStateChangedEvent event) {
      if (!event.getChecked()) {
         // Forbid deselection
         profilesViewer.setChecked(event.getElement(), true);
      }
      else {
         checkedProfile = (IJMLProfile) event.getElement();
         updatePageCompleted();
         // Ensure that only one element is selected
         Object[] checkedElements = profilesViewer.getCheckedElements();
         for (Object element : checkedElements) {
            if (element != event.getElement()) {
               profilesViewer.setChecked(element, false);
            }
         }
      }
   }
   
   protected void handleProfileSelectionChanged(SelectionChangedEvent event) {
      updateButtonsEnabledState();
   }

   protected void exportProfile() {
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
            LogUtil.getLogger().logError(e1);
         }
         catch (final IOException e1) {
            LogUtil.getLogger().logError(e1);
            LogUtil.getLogger().openErrorDialog(getShell(), 
                                                "Failed to write the exported file",
                                                "Due to an error: " + e1.getMessage(),
                                                e1);
         }
      }
   }

   protected void importProfile() {
      final FileDialog dialog = new FileDialog(
            JMLProfilePropertiesPage.this.getShell(), SWT.OPEN);
      final String[] filterNames = new String[] { "XML File" };
      final String[] filterExtensions = new String[] { "*.xml" };
      dialog.setFilterNames(filterNames);
      dialog.setFilterExtensions(filterExtensions);
      final String file = dialog.open();
      if (file != null) {
         try {
            String content = IOUtil.readFrom(new File(file));
            final IDerivedProfile profile = ProfilePersistenceFactory
                  .createDerivedProfilePersistence().read(content);
            JMLProfileManagement.instance()
                  .addUserDefinedProfile(profile);
            JMLProfilePropertiesPage.this.updateProfileViewer();
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

   protected void deleteProfile() {
      final IJMLProfile selectedProfile = getSelectedProfile();
      if (!(selectedProfile instanceof IDerivedProfile) || 
          !JMLProfileManagement.instance().isUserDefinedProfile((IDerivedProfile) selectedProfile)) {
         // Cannot occur because button is disabled, but prevent cast exception altough
         return;
      }
      if (!JMLProfileHelper.getProjectsUsingProfile(selectedProfile).isEmpty()) {
         MessageDialog.openError(getShell(),
                                 "Cannot delete profile",
                                 "Cannot delete the profile \"" + selectedProfile.getName() + "\" because some projects in the workspace are using it.");
      }
      else {
         try {
            JMLProfileManagement.instance().removeUserDefinedProfile((IDerivedProfile) selectedProfile);
            JMLProfilePropertiesPage.this.updateProfileViewer();
         }
         catch (final InvalidProfileException ie) {
            // Should not occur here, but in the case that, handle it
            LogUtil.getLogger().logError(ie);
            LogUtil.getLogger().openErrorDialog(getShell(), "Failed to write profiles", null, ie);
         }
      }
   }
   
   protected void createNewProfile() {
      IJMLProfile newProfile = JMLProfileWizard.openWizard(getShell(), null);
      if (newProfile != null) {
         updateProfileViewer();
         profilesViewer.setSelection(SWTUtil.createSelection(newProfile));
      }
   }
   
   protected void editProfile() {
      IJMLProfile modifiedProfile = JMLProfileWizard.openWizard(getShell(), getSelectedProfile());
      if (modifiedProfile != null) {
         JMLProfilePropertiesPage.this.updateProfileViewer();
      }
   }

   private Button createTableSideButton(final Composite myComposite, final String name) {
      final Button button = new Button(myComposite, SWT.PUSH);
      button.setText(name);
      button.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false, 1, 1));
      return button;
   }

   private IJMLProfile getSelectedProfile() {
      return (IJMLProfile)SWTUtil.getFirstElement(profilesViewer.getSelection());
   }

   private void updateProfileViewer() {
      List<IJMLProfile> allProfiles = JMLProfileManagement.instance().getAvailableProfilesSortedByName();
      profilesViewer.setInput(allProfiles);
      updatePageCompleted();
   }
   
   protected void updatePageCompleted() {
      if (checkedProfile != null && ((List<?>) profilesViewer.getInput()).contains(checkedProfile)) {
         setValid(true);
         setErrorMessage(null);
      }
      else {
         setValid(false);
         setErrorMessage("Default profile is not defined.");
      }
   }

   private void updateButtonsEnabledState() {
      IJMLProfile selectedProfile = getSelectedProfile();
      if (selectedProfile != null) {
         final boolean profileDerived = (selectedProfile instanceof IDerivedProfile);
         if (profileDerived) {
            editViewButton.setText("Edit...");
         }
         else {
            editViewButton.setText("View...");
         }
         editViewButton.setEnabled(true);
         exportButton.setEnabled(profileDerived);
         deleteButton.setEnabled(profileDerived && JMLProfileManagement.instance().isUserDefinedProfile((IDerivedProfile) selectedProfile));
      }
      else {
         editViewButton.setEnabled(false);
         exportButton.setEnabled(false);
         deleteButton.setEnabled(false);
      }
   }

   @Override
   protected void doStatusChanged() {
      // Enable the list in preferences always and in project if project
      // specific settings are allowed
      this.setProvileViewerEnabled(!this.isProjectPreferencePage() || this.useProjectSettings());
   }

   /**
    * Sets the list of profiles enabled or not.
    *
    * @param enabled
    *           whether to enable the list or not
    */
   private void setProvileViewerEnabled(final boolean enabled) {
      this.profilesViewer.getTable().setEnabled(enabled);
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      // We have project specific options if a property is set on the project
      return project != null && JMLPreferencesHelper.hasProjectJMLProfile(project);
   }

   @Override
   protected void enableProjectSpecificSettings(final boolean useProjectSpecificSettings) {
      super.enableProjectSpecificSettings(useProjectSpecificSettings);
      this.setProvileViewerEnabled(useProjectSpecificSettings);
   }

   @Override
   protected String getPreferencePageID() {
      return JML_PROFILE_PREF_ID;
   }

   @Override
   protected String getPropertyPageID() {
      return JML_PROFILE_PROP_ID;
   }

   private IJMLProfile getCurrentProfile() {
      if (hasProjectSpecificOptions(getProject())) {
         return JMLPreferencesHelper.getProjectActiveJMLProfile(getProject());
      }
      else {
         return JMLPreferencesHelper.getDefaultJMLProfile();
      }
   }

   private IJMLProfile getCheckedProfile() {
      Object[] checked = profilesViewer.getCheckedElements();
      if (!ArrayUtil.isEmpty(checked)) {
         return (IJMLProfile) checked[0];
      }
      else {
         return null;
      }
   }

   @Override
   protected void performDefaults() {
      checkedProfile = JMLPreferencesHelper.getDefaultDefaultJMLProfile();
      updateProfileViewer();
      super.performDefaults();
   }

   @Override
   public void performApply() {
      this.updatePreferences();
   }

   @Override
   public boolean performOk() {
      return super.performOk() && this.updatePreferences();
   }

   private boolean updatePreferences() {

      final IJMLProfile checkedProfile = this.getCheckedProfile();

      // Only write into properties if a selection is available (user is forced to),
      if (checkedProfile == null && !this.useProjectSettings()) {
         return false;
      }

      // Create a runnable which applies to changes to the preferences
      Set<IProject> affectedProjects = null;
      final Runnable preferencesUpdater;
      if (this.isProjectPreferencePage()) {
         // Only write into properties if a selection is available (user
         // is forced
         // to)
         if (this.useProjectSettings() && checkedProfile == null) {
            return false;
         }
         // Project preferences
         final IProject project = this.getProject();
         // Check whether the effective profile for the project changed
         if (useProjectSettings() ?
             checkedProfile == getCurrentProfile() :
             JMLPreferencesHelper.getDefaultJMLProfile() == getCurrentProfile()) {
            affectedProjects = Collections.emptySet();
         }
         else {
            affectedProjects = Collections.singleton(project);
         }
         preferencesUpdater = new Runnable() {
            @Override
            public void run() {
               try {
                  if (JMLProfilePropertiesPage.this.useProjectSettings()) {
                     // Set property
                     JMLPreferencesHelper.setProjectJMLProfile(project, checkedProfile);
                  }
                  else {
                     // Remove property
                     JMLPreferencesHelper.setProjectJMLProfile(project, null);
                  }
               }
               catch (final CoreException e) {
                  LogUtil.getLogger().logError("Failed to store preferences", e);
               }
            }
         };
      }
      else {
         // Check whether the affective profile has changed
         if (checkedProfile == getCurrentProfile()) {
            // Then we do not need to do a rebuild
            affectedProjects = Collections.emptySet();
         }
         else {
            affectedProjects = JMLProfileHelper.getProjectsUsingWorkspaceProfile();
         }
         preferencesUpdater = new Runnable() {
            @Override
            public void run() {
               JMLPreferencesHelper.setDefaultJMLProfile(checkedProfile);
            }
         };
      }
      // Now trigger a rebuild for these projects and update the preferences
      return RebuildHelper.triggerRebuild(affectedProjects, 
                                          getShell(), 
                                          UserMessage.ACTIVE_PROFILE_CHANGED, 
                                          preferencesUpdater);
   }
}
