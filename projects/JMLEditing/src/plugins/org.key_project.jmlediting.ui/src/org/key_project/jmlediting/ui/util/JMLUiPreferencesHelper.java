package org.key_project.jmlediting.ui.util;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.graphics.RGB;
import org.key_project.jmlediting.ui.Activator;

/**
 * This class provides Methods to manipulate the JML Preferences for the UI.
 *
 * @author Thomas Glaser
 *
 */
public final class JMLUiPreferencesHelper {

   /**
    * This enum specifies all available color properties.
    *
    * @author Moritz Lichter
    *
    */
   public static enum ColorProperty {

      /**
       * The general color for the comment.
       */
      COMMENT(new RGB(85, 80, 10), "JML Comment Color"),
      /**
       * The color for toplevel keywords.
       */
      TOPLEVEL_KEYWORD(new RGB(200, 0, 100), "JML Toplevel Keyword Color"),
      /**
       * The color for all other keywords.
       */
      KEYWORD(new RGB(100, 0, 200), "JML Keyword Color");

      /**
       * The default value.
       */
      private final RGB defaultValue;
      /**
       * The property name.
       */
      private final String name;

      /**
       * Creates a new ColorProperty.
       * 
       * @param defaultValue
       *           default value
       * @param name
       *           name
       */
      private ColorProperty(final RGB defaultValue, final String name) {
         this.defaultValue = defaultValue;
         this.name = name;
      }

      /**
       * Returns the default color for this property.
       *
       * @return the default color
       */
      public RGB getDefaultColor() {
         return this.defaultValue;
      }

      /**
       * Returns the name of the property.
       * 
       * @return the property name
       */
      public String getPropertyName() {
         return this.name;
      }
   }

   /**
    * The name of the JML profile property of a project.
    */
   public static final String JML_COMMENT_COLOR_PREFIX = "org.key_project.jmlediting.ui.color.";

   /**
    * no instantiations.
    */
   private JMLUiPreferencesHelper() {

   }

   /**
    * Changes the property value of the given JML color in the Eclipse
    * preferences.
    *
    * @param color
    *           the new color to be set
    * @param property
    *           the color property to set the color for
    */
   public static void setDefaultJMLColor(final RGB color,
         final ColorProperty property) {
      if (color == null) {
         throw new IllegalArgumentException("Cannot set a null default color");
      }
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      // global properties
      preferences.put(JML_COMMENT_COLOR_PREFIX + property.toString(),
            rgbToString(color));
   }

   /**
    * Resets the active color for the given property to default.
    *
    * @param property
    *           the property to reset.
    */
   public static void resetToDefault(final ColorProperty property) {
      setDefaultJMLColor(property.getDefaultColor(), property);
   }

   /**
    * Returns the workspace default color for the given property.
    *
    * @param property
    *           the color property to get the color for
    * @return the current set JML color of the workspace, if no was set
    */
   public static RGB getWorkspaceJMLColor(final ColorProperty property) {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final String colorString = preferences.get(JML_COMMENT_COLOR_PREFIX
            + property.toString(), null);
      // if no color was set, return the default one
      if (colorString == null) {
         return property.getDefaultColor();
      }
      final RGB color = stringtoRGB(colorString);
      // if the color could'nt be converted, return the default one
      if (color == null) {
         return property.getDefaultColor();
      }

      return color;

   }

   /**
    * Changes the String col in a RGB-representation of a color. The format of
    * the string is the outcome of the method RGB.toString()
    *
    * @param col
    *           the string should have the format RGB {x, y, z}
    * @return the RGB representation
    */
   private static RGB stringtoRGB(final String col) {
      try {
         final String[] colors = col.split(",");
         final RGB color = new RGB(Integer.parseInt(colors[0].trim()),
               Integer.parseInt(colors[1].trim()), Integer.parseInt(colors[2]
                     .trim()));

         return color;
      }
      catch (final NumberFormatException e) {
         return null;
      }
   }

   /**
    * Converts the given RGB color to a String.
    *
    * @param rgb
    *           the color to convert
    * @return the result string
    */
   private static String rgbToString(final RGB rgb) {
      return rgb.red + "," + rgb.green + "," + rgb.blue;
   }

   /**
    * Add a new PreferenceListener to the EclipsePreferences which listens to
    * changes of JML colors.
    *
    * @param listener
    *           the listener to be added
    * @return the newListener added to the Preferences
    */
   public static IPreferenceChangeListener addPreferencesListener(
         final IPreferenceChangeListener listener) {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final IPreferenceChangeListener newListener = new IPreferenceChangeListener() {
         @Override
         public void preferenceChange(final PreferenceChangeEvent event) {
            if (event.getKey() != null
                  && event.getKey().startsWith(JML_COMMENT_COLOR_PREFIX)) {
               listener.preferenceChange(event);
            }
         }
      };
      preferences.addPreferenceChangeListener(newListener);
      return newListener;

   }

   /**
    * remove the listener from the EclipsePreferences.
    *
    * @param listener
    *           the listener to be removed
    */
   public static void removePreferencesListener(
         final IPreferenceChangeListener listener) {
      InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID)
            .removePreferenceChangeListener(listener);
   }
}
