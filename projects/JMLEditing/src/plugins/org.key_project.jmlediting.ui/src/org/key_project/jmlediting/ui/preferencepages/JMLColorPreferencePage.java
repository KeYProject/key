package org.key_project.jmlediting.ui.preferencepages;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;

/**
 * The {@link JMLProfilePropertiesPage} implements a properties and preferences
 * page to show in project settings or global preferences. The page allows the
 * user to select the colors
 *
 * @author Thomas Glaser, Moritz Lichter, Lisa Eisenhardt
 *
 */
@SuppressWarnings("restriction")
public class JMLColorPreferencePage extends PropertyAndPreferencePage {

   /**
    * The ID of the page when acting as preference page.
    */
   public static final String JML_COLOUR_PREF_ID = "org.key_project.jmlediting.ui.preferences.color";

   /**
    * Needed to get the button in SWTBot for testing.
    */
   public static final String TEST_KEY = "CommentColor";

   private final Map<ColorProperty, ColorSelector> colorSelectorMap;

   /**
    * A {@link ColorSelector} which selects the Color for the JML-Comments.
    */
   // private ColorSelector commentColorSelector;

   /**
    * Creates a new {@link JMLProfilePropertiesPage}.
    */
   public JMLColorPreferencePage() {
      this.colorSelectorMap = new HashMap<JMLUiPreferencesHelper.ColorProperty, ColorSelector>();
   }

   @Override
   protected Control createPreferenceContent(final Composite parent) {
      // Initialize the UI

      final Composite myComposite = new Composite(parent, SWT.NONE);

      final GridLayout layout = new GridLayout();
      layout.numColumns = 2;

      myComposite.setLayout(layout);

      for (final ColorProperty property : ColorProperty.values()) {
         final Label label = new Label(myComposite, SWT.NONE);
         label.setText(property.getPropertyName() + ":");

         final ColorSelector colorSelector = new ColorSelector(myComposite);
         // Make selector available in SWT bot tests
         colorSelector.getButton()
               .setData(TEST_KEY, property.getPropertyName());
         colorSelector.getButton().setData(colorSelector);

         this.colorSelectorMap.put(property, colorSelector);

      }

      this.updateValues();

      return myComposite;

   }

   /**
    * Updates the values in the properties or preferences (with respect whether
    * the pane is used for preferences or properties).
    */
   private void updateValues() {
      for (final Entry<ColorProperty, ColorSelector> propertyEntry : this.colorSelectorMap
            .entrySet()) {
         final ColorSelector selector = propertyEntry.getValue();
         if (selector.getButton().isDisposed()) {
            continue;
         }
         selector.setColorValue(JMLUiPreferencesHelper
               .getWorkspaceJMLColor(propertyEntry.getKey()));
      }
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
      for (final Entry<ColorProperty, ColorSelector> propertyEntry : this.colorSelectorMap
            .entrySet()) {
         propertyEntry.getValue().setColorValue(
               propertyEntry.getKey().getDefaultColor());
      }
      super.performDefaults();

   }

   @Override
   public boolean performOk() {
      // Update values
      for (final Entry<ColorProperty, ColorSelector> propertyEntry : this.colorSelectorMap
            .entrySet()) {
         JMLUiPreferencesHelper.setDefaultJMLColor(propertyEntry.getValue()
               .getColorValue(), propertyEntry.getKey());
      }
      return super.performOk();
   }

}
