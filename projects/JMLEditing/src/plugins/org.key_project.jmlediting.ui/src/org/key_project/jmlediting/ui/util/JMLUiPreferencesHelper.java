package org.key_project.jmlediting.ui.util;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.graphics.RGB;
import org.key_project.jmlediting.ui.Activator;

/**
 * This class provides Methods to manipulate the JML Preferences for the UI
 *
 * @author Thomas Glaser
 *
 */
public final class JMLUiPreferencesHelper {

   /**
    * The name of the JML profile property of a project.
    */
   public static final String JML_COMMENT_COLOR_KEY = "org.key_project.jmleiditing.ui.CommentColor";

   /**
    * no instantiations
    */
   private JMLUiPreferencesHelper() {

   }

   /**
    * changes the property of the default JML Color in the Eclipse preferences
    *
    * @param color
    *           the new DefaultJMLColor to be set
    */
   public static void setDefaultJMLColor(final RGB color) {
      if (color == null) {
         throw new IllegalArgumentException("Cannot set a null default color");
      }
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      // global properties
      preferences.put(JML_COMMENT_COLOR_KEY, rgbToString(color));

   }

   /**
    *
    * @return the current set JML color of the workspace, if no was set
    */
   public static RGB getWorkspaceJMLColor() {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final String colorString = preferences.get(JML_COMMENT_COLOR_KEY, null);
      // if no color was set, return the default one
      if (colorString == null) {
         return getDefaultJMLColor();
      }
      final RGB color = stringtoRGB(colorString);
      // if the color could'nt be converted, return the default one
      if (color == null) {
         return getDefaultJMLColor();
      }

      return color;

   }

   /**
    * get the default JML Color the JMLComments get highlighted with.
    *
    * @return the default JML Color
    */
   public static RGB getDefaultJMLColor() {
      return new RGB(64, 0, 128);
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

   private static String rgbToString(final RGB rgb) {
      return rgb.red + "," + rgb.green + "," + rgb.blue;
   }

   /**
    * add a new PreferenceListener to the EclipsePreferences
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
            if (JML_COMMENT_COLOR_KEY.equals(event.getKey())) {
               listener.preferenceChange(event);
            }
         }
      };
      preferences.addPreferenceChangeListener(newListener);
      return newListener;

   }

   /**
    * remove the listener from the EclipsePreferences
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
