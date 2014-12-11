package org.key_project.jmlediting.ui.preferencepages;

import org.eclipse.core.resources.IProject;
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
    * Needed to get the button in SWTBot for testing
    */
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
   private ColorSelector commentColorSelector;

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

      this.commentColorSelector = new ColorSelector(myComposite);
      this.commentColorSelector.getButton().setData(TEST_KEY, "CommentColor");
      this.commentColorSelector.getButton().setData(this.commentColorSelector);

      this.updateValues();

      return myComposite;

   }

   /**
    * Updates the values in the properties or preferences (with respect whether
    * the pane is used for preferences or properties).
    */
   private void updateValues() {
      if (this.commentColorSelector.getButton().isDisposed()) {
         return;
      }

      final RGB color = JML_UIPreferencesHelper.getWorkspaceJMLColor();

      this.commentColorSelector.setColorValue(color);
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      return false;
   }

   @Override
   protected void enableProjectSpecificSettings(
         final boolean useProjectSpecificSettings) {
      super.enableProjectSpecificSettings(false);
   }

   @Override
   protected String getPreferencePageID() {
      return JML_COLOUR_PREF_ID;
   }

   @Override
   protected String getPropertyPageID() {
      return null;
   }

   @Override
   public void performDefaults() {
      this.commentColorSelector.setColorValue(JML_UIPreferencesHelper
            .getDefaultJMLColor());
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
      JML_UIPreferencesHelper.setDefaultJMLColor(this.commentColorSelector
            .getColorValue());

      InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID)
      .removePreferenceChangeListener(this.currentPreferenceListener);
      return super.performOk();
   }

}
