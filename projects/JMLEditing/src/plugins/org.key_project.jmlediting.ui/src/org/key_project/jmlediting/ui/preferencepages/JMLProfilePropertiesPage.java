package org.key_project.jmlediting.ui.preferencepages;

import java.util.NoSuchElementException;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
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
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.Activator;
import org.key_project.jmlediting.ui.profileEditor.ProfileViewDialog;

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
   private Button viewProfileButton;
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
   }

   @Override
   public void setVisible(boolean visible) {
      // Register the preference listener if the dialog is visible
      // do not generate memory leaks, listener are removed in
      // performOK and performCancel, here is too late
      if (visible) {
         this.currentPreferenceListener = JMLPreferencesHelper
               .buildDefaultProfilePreferencesListener(new IPreferenceChangeListener() {

                  @Override
                  public void preferenceChange(final PreferenceChangeEvent event) {
                     updateSelection(false);
                  }
               });
      }
      super.setVisible(visible);
   }

   private Button createTableSideButton(Composite myComposite, String name) {
      Button button = new Button(myComposite, SWT.PUSH);
      button.setText(name);
      button.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false, 1, 1));

      return button;
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
      Label label = new Label(myComposite, SWT.NONE);
      label.setText("Choose active JML Profile from available ones:");
      label.setLayoutData(data);

      data = new GridData(GridData.FILL_BOTH);
      data.horizontalSpan = 1;
      data.verticalSpan = 4;

      this.profilesList = new Table(myComposite, SWT.V_SCROLL | SWT.SINGLE
            | SWT.FULL_SELECTION | SWT.CHECK | SWT.BORDER);
      this.profilesList.setLayoutData(data);
      this.profilesList.setLinesVisible(true);
      this.profilesList.setHeaderVisible(true);

      data = new GridData();
      data.horizontalSpan = 1;
      data.verticalAlignment = SWT.TOP;
      data.horizontalAlignment = SWT.FILL;

      this.viewProfileButton = this.createTableSideButton(myComposite,
            " View ... ");

      this.initUI();

      this.viewProfileButton.addSelectionListener(new SelectionListener() {

         @Override
         public void widgetSelected(SelectionEvent e) {
            ProfileViewDialog d = new ProfileViewDialog(
                  JMLProfilePropertiesPage.this.getShell());
            d.setProfile(allProfiles.get(0));
            d.open();
         }

         @Override
         public void widgetDefaultSelected(SelectionEvent e) {
         }
      });

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
      TableColumn nameColumn = new TableColumn(this.profilesList, SWT.LEFT);
      nameColumn.setMoveable(false);
      nameColumn.setWidth(300);
      nameColumn.setText("Profile Name");
      for (IJMLProfile profile : this.allProfiles) {
         TableItem item = new TableItem(this.profilesList, 0);
         item.setText(new String[] { profile.getName() });
      }

      // Make sure that only one profile is available at a single time
      this.profilesList.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event event) {
            if (event.detail == SWT.CHECK) {
               TableItem item = (TableItem) event.item;
               if (item.getChecked()) {
                  for (TableItem item2 : profilesList.getItems()) {
                     if (item != item2) {
                        item2.setChecked(false);
                     }
                  }
                  setErrorMessage(null);
               }
               else {
                  boolean nothingChecked = true;
                  for (TableItem item2 : profilesList.getItems()) {
                     if (item2.getChecked()) {
                        nothingChecked = false;
                        break;
                     }
                  }
                  if (nothingChecked) {
                     setErrorMessage("Please select an active profile");
                  }
               }
            }
         }
      });

      this.updateSelection(false);

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

      this.viewProfileButton.setEnabled(enabled);
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      // We have project specific options if a property is set on the project
      return JMLPreferencesHelper.hasProjectJMLProfile(project);
   }

   @Override
   protected void enableProjectSpecificSettings(
         boolean useProjectSpecificSettings) {
      super.enableProjectSpecificSettings(useProjectSpecificSettings);
      if (!useProjectSpecificSettings) {
         // Reset selection to default if no project settings
         this.updateSelection(true);
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
   private void updateSelection(boolean forceDefault) {
      IJMLProfile currentProfile = null;
      if (!forceDefault
            && (this.isProjectPreferencePage() && this.useProjectSettings())) {
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
         catch (NoSuchElementException e) {
            this.setErrorMessage("No JML Profile available");
            return;
         }

      }

      // Select profile in the list
      for (TableItem item : this.profilesList.getItems()) {
         item.setChecked(false);
      }
      if (currentProfile != null) {
         int index = this.allProfiles.indexOf(currentProfile);
         if (index != -1) {
            this.profilesList.getItem(index).setChecked(true);
         }
         else {
            this.setErrorMessage("Profile \"" + currentProfile.getName()
                  + "\" is not available.");
         }
      }
      // Redraw the list because selection is otherwise not always cleared
      this.profilesList.redraw();
   }

   private void removePreferencesListener() {
      JMLPreferencesHelper
            .removeDefaultProfilePreferencesListener(this.currentPreferenceListener);
   }

   @Override
   public boolean performCancel() {
      boolean cancel = super.performCancel();
      if (cancel) {
         // Remove preferences listener
         this.removePreferencesListener();
      }
      return cancel;
   }

   @Override
   public boolean performOk() {

      IJMLProfile selectedProfile = null;
      for (int i = 0; i < this.profilesList.getItemCount(); i++) {

         // Can only have one selection
         if (this.profilesList.getItem(i).getChecked()) {
            selectedProfile = this.allProfiles.get(i);
            break;
         }
      }

      // Only write into properties if a selection is available (user is forced
      // to),
      if (selectedProfile == null && !this.useProjectSettings()) {
         return false;
      }

      if (this.isProjectPreferencePage()) {
         // Project preferences
         IProject project = this.getProject();
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
         catch (CoreException e) {
            return false;
         }
      }
      else {
         JMLPreferencesHelper.setDefaultJMLProfile(selectedProfile);
      }

      boolean ok = super.performOk();
      if (ok) {
         // Window is closed, remove listener
         this.removePreferencesListener();
      }
      return ok;
   }

}
