package org.key_project.sed.key.evaluation.model.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.sed.key.evaluation.model.Activator;

/**
 * The SED Server settings.
 * @author Martin Hentschel
 */
public class ServerPreferences {
   /**
    * Preference key to set the host.
    */
   public static final String HOST = "org.key_project.sed.key.evaluation.model.host";
   
   /**
    * Preference key to set the port.
    */
   public static final String PORT = "org.key_project.sed.key.evaluation.model.port";
   
   /**
    * Returns the managed {@link IPreferenceStore}.
    * @return The managed {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the host.
    * @return The host.
    */
   public static String getHost() {
      return getStore().getString(HOST);
   }
   
   /**
    * Returns the default host.
    * @return The default host.
    */
   public static String getDefaultHost() {
      return getStore().getDefaultString(HOST);
   }
   
   /**
    * Sets the host.
    * @param value The host.
    */
   public static void setHost(String value) {
      getStore().setValue(HOST, value);
   }
   
   /**
    * Sets the default host.
    * @param defaultValue The default host.
    */
   public static void setDefaultHost(String defaultValue) {
      getStore().setDefault(HOST, defaultValue);
   }
   
   /**
    * Returns the port.
    * @return The port.
    */
   public static int getPort() {
      return getStore().getInt(PORT);
   }
   
   /**
    * Returns the default port.
    * @return The default port.
    */
   public static int getDefaultPort() {
      return getStore().getDefaultInt(PORT);
   }
   
   /**
    * Sets the port.
    * @param value The port.
    */
   public static void setPort(int value) {
      getStore().setValue(PORT, value);
   }
   
   /**
    * Sets the default port.
    * @param defaultValue The default port.
    */
   public static void setDefaultPort(int defaultValue) {
      getStore().setDefault(PORT, defaultValue);
   }
}
