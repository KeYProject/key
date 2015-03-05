package org.key_project.jmlediting.ui.preferencepages;

import java.util.NoSuchElementException;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
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
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.preferencepages.profileEditor.ProfileEditorDialog;

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
   private Table profilesList;
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
    * needs to be global to change label-text
    */
   private Button editViewButton;

   /**
    * Creates a new {@link JMLProfilePropertiesPage}.
    */
   public JMLProfilePropertiesPage() {
   }

   @Override
   public void setVisible(final boolean visible) {
      // Register the preference listener if the dialog is visible
      // do not generate memory leaks, listener are removed in
      // performOK and performCancel, here is too late
      if (visible) {
         this.currentPreferenceListener = JMLPreferencesHelper
               .buildDefaultProfilePreferencesListener(new IPreferenceChangeListener() {
                  @Override
                  public void preferenceChange(final PreferenceChangeEvent event) {
                     if (!JMLProfilePropertiesPage.this.profilesList
                           .isDisposed()) {
                        JMLProfilePropertiesPage.this.updateSelection();
                     }
                  }
               });
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

      this.profilesList = new Table(myComposite, SWT.H_SCROLL | SWT.V_SCROLL
            | SWT.BORDER | SWT.CHECK | SWT.FULL_SELECTION);
      this.profilesList.setLayoutData(data);
      this.profilesList.setLinesVisible(true);
      this.profilesList.setHeaderVisible(true);

      this.initUI();

      this.editViewButton = this.createTableSideButton(myComposite, "Edit");
      final Button exportButton = this.createTableSideButton(myComposite,
            "Export");
      final Button importButton = this.createTableSideButton(myComposite,
            "Import");
      final Button newButton = this.createTableSideButton(myComposite, "New");

      this.updateSelection();

      exportButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            System.out.println("click Export");
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      importButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            System.out.println("click Import");
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      newButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            System.out.println("click New");
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      this.editViewButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            final ProfileEditorDialog d = new ProfileEditorDialog(
                  JMLProfilePropertiesPage.this.getShell());
            d.setProfile(JMLProfilePropertiesPage.this.getSelectedProfile());
            d.open();
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
      // Get all profiles and set them to the list
      this.allProfiles = JMLProfileManagement
            .getAvailableProfilesSortedByName();
      final TableColumn nameColumn = new TableColumn(this.profilesList,
            SWT.LEFT);
      nameColumn.setMoveable(false);
      nameColumn.setWidth(175);
      nameColumn.setText("Profile Name");
      final TableColumn typeColumn = new TableColumn(this.profilesList,
            SWT.LEFT);
      typeColumn.setMoveable(false);
      typeColumn.setWidth(175);
      typeColumn.setText("Profile Type");
      for (final IJMLProfile profile : this.allProfiles) {
         final TableItem item = new TableItem(this.profilesList, 0);
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

      // Make sure that only one profile is available at a single time
      this.profilesList.addListener(SWT.Selection, new Listener() {
         @Override
         public void handleEvent(final Event event) {
            if (event.detail == SWT.CHECK) {
               final TableItem item = (TableItem) event.item;
               if (item.getChecked()) {
                  final IJMLProfile profile = JMLProfilePropertiesPage.this.allProfiles
                        .get(JMLProfilePropertiesPage.this.profilesList
                              .indexOf(item));
                  JMLProfilePropertiesPage.this
                        .updateEditViewButtonLabel(profile);
                  for (final TableItem item2 : JMLProfilePropertiesPage.this.profilesList
                        .getItems()) {
                     if (item != item2) {
                        item2.setChecked(false);
                     }
                  }
                  JMLProfilePropertiesPage.this.setErrorMessage(null);
               }
               else {
                  boolean nothingChecked = true;
                  for (final TableItem item2 : JMLProfilePropertiesPage.this.profilesList
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
         }
      });

   }

   private boolean isProfileDerived(final IJMLProfile profile) {
      return profile instanceof IDerivedProfile;
   }

   private IJMLProfile getProfileForTableItem(final TableItem item) {
      return JMLProfilePropertiesPage.this.allProfiles
            .get(JMLProfilePropertiesPage.this.profilesList.indexOf(item));
   }

   private void updateEditViewButtonLabel(final IJMLProfile profile) {
      if (this.editViewButton == null) {
         return;
      }

      if (this.isProfileDerived(profile)) {
         JMLProfilePropertiesPage.this.editViewButton.setText("Edit");
      }
      else {
         JMLProfilePropertiesPage.this.editViewButton.setText("View");
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
      this.profilesList.setEnabled(enabled);
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
      for (final TableItem item : this.profilesList.getItems()) {
         item.setChecked(false);
      }
      final int index = this.allProfiles.indexOf(currentProfile);
      if (index != -1) {
         this.profilesList.getItem(index).setChecked(true);
      }
      else {

         this.setErrorMessage("Profile \"" + currentProfile.getName()
               + "\" is not available.");
      }

      this.updateEditViewButtonLabel(currentProfile);

      // Redraw the list because selection is otherwise not always cleared
      this.profilesList.redraw();
   }

   private void removePreferencesListener() {
      JMLPreferencesHelper
            .removeDefaultProfilePreferencesListener(this.currentPreferenceListener);
   }

   @Override
   public boolean performCancel() {
      final boolean cancel = super.performCancel();
      if (cancel) {
         // Remove preferences listener
         this.removePreferencesListener();
      }
      return cancel;
   }

   private IJMLProfile getSelectedProfile() {
      for (int i = 0; i < this.profilesList.getItemCount(); i++) {
         // Can only have one selection
         if (this.profilesList.getItem(i).getChecked()) {
            return this.allProfiles.get(i);
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
            return false;
         }
      }
      else {
         JMLPreferencesHelper.setDefaultJMLProfile(selectedProfile);
      }

      final boolean ok = super.performOk();
      if (ok) {
         // Window is closed, remove listener
         this.removePreferencesListener();
      }
      return ok;
   }

}
