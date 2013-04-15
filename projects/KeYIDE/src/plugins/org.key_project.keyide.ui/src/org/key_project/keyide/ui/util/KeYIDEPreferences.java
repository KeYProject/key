package org.key_project.keyide.ui.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.keyide.ui.Activator;

/**
 * <p>
 * Provides access to the preferences of the KeY visualization.
 * </p>
 * <p>
 * Default values are defined via {@link KeYIDEPreferencesInitializer}.
 * </p>
 * @author Marco Drebing, Niklas Bunzel, Christoph Schneider, Stefan Käsdorf
 */
public class KeYIDEPreferences {
   /**
    * Preference key for the maximal number of set nodes per branch on run.
    */
   public static final String SWITCH_TO_KEY_PERSPECTIVE = "org.key_project.keyide.ui.visualization.switchToKeyPerspective";

   /**
    * Returns the managed {@link IPreferenceStore}.
    * @return The managed {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the property which defines the behavior when a switch to the key perspective is requested.
    * @return The property which defines the behavior when a switch to the key perspective is requested.
    */
   public static String getSwitchToKeyPerspective() {
      return getStore().getString(SWITCH_TO_KEY_PERSPECTIVE);
   }
   
   /**
    * Returns the default property which defines the behavior when a switch to the key perspective is requested.
    * @return The default property which defines the behavior when a switch to the key perspective is requested.
    */
   public static String getDefaultSwitchToKeyPerspective() {
      return getStore().getDefaultString(SWITCH_TO_KEY_PERSPECTIVE);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the key perspective is requested.
    * @param value The property which defines the behavior when a switch to the key perspective is requested.
    */
   public static void setSwitchToKeyPerspective(String value) {
      getStore().setValue(SWITCH_TO_KEY_PERSPECTIVE, value);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the state key perspective is requested.
    * @param defaultValue The default property which defines the behavior when a switch to the key perspective is requested.
    */
   public static void setDefaultSwitchToKeyPerspective(String defaultValue) {
      getStore().setDefault(SWITCH_TO_KEY_PERSPECTIVE, defaultValue);
   }
}
