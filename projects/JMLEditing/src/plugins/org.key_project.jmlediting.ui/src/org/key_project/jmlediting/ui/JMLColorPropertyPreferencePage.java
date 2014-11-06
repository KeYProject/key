package org.key_project.jmlediting.ui;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.ColorDialog;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.key_project.jmlediting.core.IJMLProfile;
import org.key_project.jmlediting.core.JMLProfileManagement;
import org.key_project.jmlediting.ui.preferences.PreferenceConstants;


   /**
    * The {@link JMLProfilePropertiesPage} implements a properties and preferences
    * page to show in project settings or global preferences. The page allows the
    * user to select a JML profile from available ones as project specific or
    * global default.
    * 
    * @author Moritz Lichter
    *
    */
   public class JMLColorPropertyPreferencePage extends PropertyAndPreferencePage
       {

      
      /**
       * The ID of the page when acting as preference page.
       */
      public static final String JML_COLOUR_PREF_ID = "org.key_project.jmlediting.ui.preferences.colour";
      /**
       * The ID of the page when acting as properties page.
       */
      public static final String JML_COLOUR_PROP_ID = "org.key_project.jmlediting.ui.propertypages.colour";
     
      private IPreferenceChangeListener currentPreferenceListener;
      
      private ColorFieldEditor CommentColor;
      
      public static final IPreferenceStore store = Activator.getDefault().getPreferenceStore();

          
      /**
       * Creates a new {@link JMLProfilePropertiesPage}.
       */
      public JMLColorPropertyPreferencePage() {
         this.currentPreferenceListener = new IPreferenceChangeListener(){

            @Override
            public void preferenceChange(final PreferenceChangeEvent event) {
               updateSelection();
               
            }
         }  ;


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
      protected Control createPreferenceContent(Composite parent) {
         // Initialize the UI
         // Create a list for the profile with a label
         final Composite myComposite = new Composite(parent, 0);

         //final GridLayout layout = new GridLayout();
        // layout.numColumns = 1;
         //myComposite.setLayout(layout);
         
         //GridData data;

         //data = new GridData();
         
       
         new ColorFieldEditor(PropertyNames.COMMENT_COLOR.getLocalName(), 
               "Choose JML comment color:  ", parent);
         
         
         
         
         this.initUI();
         
         

         return myComposite;
      }
      
      
      
      
      /**
       * Initlializes the content of the UI. 
       * Sets the values of all fields to the default
       */
      private void initUI() {
         // Get all profiles and set them to the list
         
        store.setDefault(PropertyNames.COMMENT_COLOR.getLocalName(), PropertyNames.DEFAULT_JML_COMMENT_COLOR.toString());
                

      }
      /**
       * Updates the selected profile in the list of profiles to match the profile
       * in the properties or preferences (with respect whether the pane is used
       * for preferences or properties).
       */
      private void updateSelection() {
         String color = null;
         if (this.isProjectPreferencePage() || this.useProjectSettings()) {
            // Read local project properties if we are in a properties pane and
            // project specific settings are enabled
            try {
               store.setValue(PropertyNames.COMMENT_COLOR.getLocalName(), 
                     this.getProject().getPersistentProperty(PropertyNames.COMMENT_COLOR));
               color="set";
            }
            catch (CoreException e) {
               color = null;
            }
         }
         // Read from global preferences if no project specific profile is set
         if (color == null) {
            // Global preferences
            //IEclipsePreferences preferences = InstanceScope.INSTANCE
                 // .getNode(Activator.PLUGIN_ID);
            store.setToDefault(PropertyNames.COMMENT_COLOR.getLocalName());
            /*color = preferences.get(
                  PropertyNames.DEFAULT_JML_COMMENT_COLOR.toString(), null);*/
         }

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
        // this.setListEnabled(useProjectSpecificSettings);
         super.enableProjectSpecificSettings(useProjectSpecificSettings);
      }
      
      @Override
      protected String getPreferencePageID() {
         return JML_COLOUR_PREF_ID;
      }

      @Override
      protected String getPropertyPageID() {
         return JML_COLOUR_PROP_ID;
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

                  

         

         if (this.isProjectPreferencePage()) {
            // Project preferences
            
            IProject project = this.getProject();
            try {
               if (this.useProjectSettings()) {
                  // Set property
                  project.setPersistentProperty(PropertyNames.COMMENT_COLOR, CommentColor.getColorSelector().getColorValue().toString());

               }
               else {
                  // Remove property
                  project.setPersistentProperty(PropertyNames.COMMENT_COLOR, null);
               }
            }
            catch (CoreException e) {
               return false;
            }
         }
         else {
            // global properties
            preferences
                  .put(PropertyNames.COMMENT_COLOR.getLocalName(), CommentColor.getColorSelector().getColorValue().toString());
         }

         return super.performOk();
      }
}
