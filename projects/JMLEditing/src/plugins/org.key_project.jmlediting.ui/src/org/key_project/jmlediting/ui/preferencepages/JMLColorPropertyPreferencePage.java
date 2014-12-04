package org.key_project.jmlediting.ui.preferencepages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
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
import org.key_project.jmlediting.ui.util.JML_UIPreferencesHelper;

/**
 * The {@link JMLProfilePropertiesPage} implements a properties and preferences
 * page to show in project settings or global preferences. The page allows the
 * user to select the colors
 *
 * @author Lisa Eisenhardt
 *
 */
@SuppressWarnings("restriction")
public class JMLColorPropertyPreferencePage extends PropertyAndPreferencePage {

   /**
    * The ID of the page when acting as preference page.
    */
   public static final String JML_COLOUR_PREF_ID = "org.key_project.jmlediting.ui.preferences.color";
   /**
    * The ID of the page when acting as properties page.
    */
   public static final String JML_COLOUR_PROP_ID = "org.key_project.jmlediting.ui.properties.color";

   /**
    * The name of the global preference for the default JML profile.
    */
   public static final RGB DEFAULT_JML_COMMENT_COLOR = new RGB(0, 255, 0);

   public static final String TEST_KEY = "CommentColor";

   /**
    * The {@link IPreferenceChangeListener} which listens to changes of the
    * profile property for properties. This is used to change the selection in
    * the properies page when global settings are used and they change.
    */
   private final IPreferenceChangeListener currentPreferenceListener;

   /**
    * A {@link ColorSelector} which selects the Color for the JML-Comments
    */
   private ColorSelector commentColor;

   /**
    * Creates a new {@link JMLProfilePropertiesPage}.
    */
   public JMLColorPropertyPreferencePage() {
      this.currentPreferenceListener = new IPreferenceChangeListener() {

         @Override
         public void preferenceChange(final PreferenceChangeEvent event) {
            JMLColorPropertyPreferencePage.this.updateValues();

         }

      };
   }

   @Override
   public void setVisible(final boolean visible) {
      // Register the preference listener if the dialog is visible
      // do not generate memory leaks, listener are removed in
      // performOK and performCancel, here is too late
      if (visible) {
         final IEclipsePreferences preferences = InstanceScope.INSTANCE
               .getNode(Activator.PLUGIN_ID);
         preferences
               .addPreferenceChangeListener(this.currentPreferenceListener);
      }
      super.setVisible(visible);
   }

   @Override
   protected Control createPreferenceContent(final Composite parent) {
      // Initialize the UI

      final Composite myComposite = new Composite(parent, SWT.NONE);

      final GridLayout layout = new GridLayout();
      layout.numColumns = 2;

      myComposite.setLayout(layout);

      GridData data;

      data = new GridData();
      final Label label = new Label(myComposite, SWT.NONE);
      label.setText("Choose JML comment color:");
      label.setLayoutData(data);

      this.commentColor = new ColorSelector(myComposite);
      this.commentColor.getButton().setData(TEST_KEY, "CommentColor");
      this.commentColor.getButton().setData(this.commentColor);
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      if (preferences.get(JML_UIPreferencesHelper.COMMENT_COLOR.getLocalName(),
            null) == null) {
         this.initializeDefaults();
      }
      this.updateValues();

      return myComposite;

   }

   /**
    * Saves the default values of the fields
    */
   private void initializeDefaults() {
      // set default Values:
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      preferences.put(JML_UIPreferencesHelper.COMMENT_COLOR.getLocalName(),
            DEFAULT_JML_COMMENT_COLOR.toString());

   }

   /**
    * Updates the values in the properties or preferences (with respect whether
    * the pane is used for preferences or properties).
    */
   private void updateValues() {

      RGB color = null;
      if (this.isProjectPreferencePage() || this.useProjectSettings()) {
         // Read local project properties if we are in a properties pane and
         // project specific settings are enabled
         color = JML_UIPreferencesHelper.getProjectJMLColor(this.getProject());
      }
      // Read from global preferences if no project specific profile is set
      if (color == null) {
         // Global preferences\
         color = JML_UIPreferencesHelper.getWorkspaceJMLColor();
      }

      this.commentColor.setColorValue(color);
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      return JML_UIPreferencesHelper.hasProjectJMLColor(project);
   }

   @Override
   protected void enableProjectSpecificSettings(
         final boolean useProjectSpecificSettings) {
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

   @Override
   public void performDefaults() {
      this.commentColor.setColorValue(DEFAULT_JML_COMMENT_COLOR);
      super.performDefaults();

   }

   @Override
   public boolean performCancel() {
      // Remove preferences listener
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      preferences
            .removePreferenceChangeListener(this.currentPreferenceListener);
      return super.performCancel();
   }

   @Override
   public boolean performOk() {
      // Remove preference listener

      if (this.isProjectPreferencePage()) {
         // Project preferences

         final IProject project = this.getProject();
         try {
            if (this.useProjectSettings()) {
               // Set property
               JML_UIPreferencesHelper.setProjectJMLColor(project,
                     this.commentColor.getColorValue());
            }
            else {
               // Remove property
               JML_UIPreferencesHelper.setProjectJMLColor(project, null);
            }
         }
         catch (final CoreException e) {
            return false;
         }
      }
      else {
         JML_UIPreferencesHelper.setDefaultJMLColor(this.commentColor
               .getColorValue());
      }

      return super.performOk();
   }

}
