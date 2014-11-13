package org.key_project.jmlediting.ui.preferencepages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.key_project.jmlediting.ui.Activator;

/**
 * The {@link JMLProfilePropertiesPage} implements a properties and preferences
 * page to show in project settings or global preferences. The page allows the
 * user to select the colours
 * 
 * @author Lisa Eisenhardt
 *
 */
@SuppressWarnings("restriction")
public class JMLColorPropertyPreferencePage extends PropertyAndPreferencePage {

   /**
    * The ID of the page when acting as preference page.
    */
   public static final String JML_COLOUR_PREF_ID = "org.key_project.jmlediting.ui.preferences.colour";
   /**
    * The ID of the page when acting as properties page.
    */
   public static final String JML_COLOUR_PROP_ID = "org.key_project.jmlediting.ui.propertypages.colour";

   /**
    * The name of the JML profile property of a project.
    */
   public static final QualifiedName COMMENT_COLOR = new QualifiedName(
         "org.key_project.jmleiditing.ui", "CommentColor");

   /**
    * The name of the global preference for the default JML profile.
    */
   public static final RGB DEFAULT_JML_COMMENT_COLOR = new RGB(0, 255, 0);

   /**
    * The {@link IPreferenceChangeListener} which listens to changes of the
    * profile property for properties. This is used to change the selection in
    * the properies page when global settings are used and they change.
    */
   private IPreferenceChangeListener currentPreferenceListener;

   /**
    * A {@link ColorSelector} which selects the Color for the JML-Comments
    */
   private ColorSelector CommentColor;

   /**
    * Creates a new {@link JMLProfilePropertiesPage}.
    */
   public JMLColorPropertyPreferencePage() {

      this.currentPreferenceListener = new IPreferenceChangeListener() {

         @Override
         public void preferenceChange(PreferenceChangeEvent event) {
            updateValues();

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
   protected Control createPreferenceContent(Composite parent) {
      // Initialize the UI

      final Composite myComposite = new Composite(parent, SWT.NONE);

      final GridLayout layout = new GridLayout();
      layout.numColumns = 1;
      myComposite.setLayout(layout);

      GridData data;

      data = new GridData();
      Label label = new Label(myComposite, SWT.NONE);
      label.setText("Choose JML comment color:");
      label.setLayoutData(data);

      CommentColor = new ColorSelector(myComposite);

      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      if (preferences.get(COMMENT_COLOR.getLocalName(), null) == null) {
         initializeDefaults();
      }
      this.updateValues();

      return myComposite;

   }

   /**
    * Saves the default values of the fields
    */
   private void initializeDefaults() {
      // set default Values:
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      preferences.put(COMMENT_COLOR.getLocalName(),
            DEFAULT_JML_COMMENT_COLOR.toString());

   }

   /**
    * Updates the values in the properties or preferences (with respect whether
    * the pane is used for preferences or properties).
    */
   private void updateValues() {
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);

      String color = null;
      if (this.isProjectPreferencePage() || this.useProjectSettings()) {
         // Read local project properties if we are in a properties pane and
         // project specific settings are enabled
         try {
            color = this.getProject().getPersistentProperty(COMMENT_COLOR);
         }
         catch (CoreException e) {
            color = null;
         }
      }
      // Read from global preferences if no project specific profile is set
      if (color == null) {
         // Global preferences
         color = preferences.get(COMMENT_COLOR.getLocalName(), null);
      }

      CommentColor.setColorValue(StringtoRGB(color));
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      // We have project specific options if a property is set on the project
      try {
         return project.getPersistentProperty(COMMENT_COLOR) != null;
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
         this.updateValues();
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

   /**
    * Changes the String col in a RGB-representation of a color. The format of
    * the string is the outcome of the method RGB.toString()
    * 
    * @param col
    *           the string should have the format RGB {x, y, z}
    * @return the RGB representation
    */

   private RGB StringtoRGB(String col) {

      String[] colors = col.substring(5, col.length() - 1).split(", ");
      RGB color = new RGB(Integer.parseInt(colors[0].trim()),
            Integer.parseInt(colors[1].trim()), Integer.parseInt(colors[2]
                  .trim()));

      return color;
   }

   @Override
   public void performDefaults() {
      CommentColor.setColorValue(DEFAULT_JML_COMMENT_COLOR);
      super.performDefaults();

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
   public void performApply() {
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);

      if (this.isProjectPreferencePage()) {
         // Project preferences

         IProject project = this.getProject();

         try {
            if (this.useProjectSettings()) {
               // Set property
               project.setPersistentProperty(COMMENT_COLOR, CommentColor
                     .getColorValue().toString());

            }
            else {
               // Remove property
               project.setPersistentProperty(COMMENT_COLOR, null);
            }
         }
         catch (CoreException e) {

         }
      }
      else {
         // global properties
         preferences.put(COMMENT_COLOR.getLocalName(), CommentColor
               .getColorValue().toString());

      }

      super.performApply();
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
               project.setPersistentProperty(COMMENT_COLOR, CommentColor
                     .getColorValue().toString());

            }
            else {
               // Remove property
               project.setPersistentProperty(COMMENT_COLOR, null);
            }
         }
         catch (CoreException e) {
            return false;
         }
      }
      else {
         // global properties
         preferences.put(COMMENT_COLOR.getLocalName(), CommentColor
               .getColorValue().toString());

      }

      return super.performOk();
   }

}
