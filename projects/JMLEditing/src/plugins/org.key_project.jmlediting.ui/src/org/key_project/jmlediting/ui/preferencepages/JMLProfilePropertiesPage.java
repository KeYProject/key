package org.key_project.jmlediting.ui.preferencepages;

import java.util.NoSuchElementException;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
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
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.IProfileManagementListener;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.preferencepages.profileDialog.JMLProfileDialog;

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
            // JMLProfilePropertiesPage.this.fillTable();
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
      final Button exportButton = this.createTableSideButton(myComposite,
            "Export...");
      final Button importButton = this.createTableSideButton(myComposite,
            "Import...");

      this.updateSelection();

      exportButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      importButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
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
                     .getSelectedProfile();
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
            final IJMLProfile profile = JMLProfilePropertiesPage.this.allProfiles
                  .get(JMLProfilePropertiesPage.this.profilesListTable
                        .indexOf(item));
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
               JMLProfilePropertiesPage.this.updateEditViewButtonLabel(profile);
               JMLProfilePropertiesPage.this.profile2EditView = profile;
            }
         }
      });

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

   private void updateEditViewButtonLabel(final IJMLProfile profile) {
      if (this.editViewButton == null) {
         return;
      }

      if (this.isProfileDerived(profile)) {
         JMLProfilePropertiesPage.this.editViewButton.setText("Edit...");
      }
      else {
         JMLProfilePropertiesPage.this.editViewButton.setText("View...");
      }
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

      this.updateEditViewButtonLabel(currentProfile);

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

   private IJMLProfile getSelectedProfile() {
      for (int i = 0; i < this.profilesListTable.getItemCount(); i++) {
         // Can only have one selection
         if (this.profilesListTable.getItem(i).getChecked()) {
            final IJMLProfile result = this.allProfiles.get(i);
            return result;
         }
      }
      return null;
   }

   @Override
   public boolean performOk() {

      final IJMLProfile selectedProfile = this.getSelectedProfile();

      // Only write into properties if a selection is available (user is forced
      // to),
      if (selectedProfile == null && !this.useProjectSettings()) {
         return false;
      }

      if (this.isProjectPreferencePage()) {
         // Project preferences
         final IProject project = this.getProject();
         try {
            if (this.useProjectSettings()) {
               // Only write into properties if a selection is available (user
               // is forced
               // to)
               if (selectedProfile == null) {
                  return false;
               }
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
            e.printStackTrace();
            return false;
         }
      }
      else {
         JMLPreferencesHelper.setDefaultJMLProfile(selectedProfile);
      }

      final boolean ok = super.performOk();
      if (ok) {
         // Window is closed, remove listener
         this.uninstallListener();
      }
      return ok;
   }

}
