package org.key_project.jmlediting.ui.util;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.graphics.RGB;
import org.key_project.jmlediting.ui.Activator;

public final class JMLUiPreferencesHelper {

   /**
    * The name of the JML profile property of a project.
    */
   public static final String JML_COMMENT_COLOR_KEY = "org.key_project.jmleiditing.ui.CommentColor";

   private JMLUiPreferencesHelper() {

   }

   public static void setDefaultJMLColor(final RGB color) {
      if (color == null) {
         throw new IllegalArgumentException("Cannot set a null default color");
      }
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      // global properties
      preferences.put(JML_COMMENT_COLOR_KEY, rgbToString(color));

   }

   public static RGB getWorkspaceJMLColor() {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final String colorString = preferences.get(JML_COMMENT_COLOR_KEY, null);
      if (colorString == null) {
         return getDefaultJMLColor();
      }
      final RGB color = stringtoRGB(colorString);
      if (color == null) {
         return getDefaultJMLColor();
      }

      return color;

   }

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

   public static void removePreferencesListener(
         final IPreferenceChangeListener listener) {
      InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID)
            .removePreferenceChangeListener(listener);
   }
}
