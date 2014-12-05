package org.key_project.jmlediting.ui.util;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.graphics.RGB;
import org.key_project.jmlediting.ui.Activator;

public final class JML_UIPreferencesHelper {

   /**
    * The name of the JML profile property of a project.
    */
   public static final QualifiedName COMMENT_COLOR = new QualifiedName(
         "org.key_project.jmleiditing.ui", "CommentColor");

   private JML_UIPreferencesHelper() {

   }

   public static void setProjectJMLColor(final IProject project, final RGB color)
         throws CoreException {
      String value = null;
      if (color != null) {
         value = color.toString();
      }
      project.setPersistentProperty(COMMENT_COLOR, value);
   }

   public static void setDefaultJMLColor(final RGB color) {
      if (color == null) {
         throw new IllegalArgumentException("Cannot set a null default color");
      }
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      // global properties
      preferences.put(JML_UIPreferencesHelper.COMMENT_COLOR.getLocalName(),
            color.toString());

   }

   public static RGB getProjectJMLColor(final IProject project) {
      try {
         final String colorString = project
               .getPersistentProperty(JML_UIPreferencesHelper.COMMENT_COLOR);
         if (colorString == null) {
            return null;
         }
         return stringtoRGB(colorString);
      }
      catch (final CoreException e) {
         return null;
      }
   }

   public static boolean hasProjectJMLColor(final IProject project) {
      return getProjectJMLColor(project) != null;
   }

   public static RGB getWorkspaceJMLColor() {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final String colorString = preferences.get(
            JML_UIPreferencesHelper.COMMENT_COLOR.getLocalName(), null);
      if (colorString == null) {
         return getDefaultJMLColor();
      }
      return stringtoRGB(colorString);

   }

   public static RGB getDefaultJMLColor() {
      return new RGB(50, 50, 50);
   }

   /**
    * Changes the String col in a RGB-representation of a color. The format of
    * the string is the outcome of the method RGB.toString()
    *
    * @param col
    *           the string should have the format RGB {x, y, z}
    * @return the RGB representation
    */

   public static RGB stringtoRGB(final String col) {

      final String[] colors = col.substring(5, col.length() - 1).split(", ");
      final RGB color = new RGB(Integer.parseInt(colors[0].trim()),
            Integer.parseInt(colors[1].trim()), Integer.parseInt(colors[2]
                  .trim()));

      return color;
   }

}
