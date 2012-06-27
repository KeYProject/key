package org.key_project.sed.key.core.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.sed.key.core.Activator;

/**
 * <p>
 * Provides access to the preferences of the Symbolic Execution Debugger based on KeY.
 * </p>
 * <p>
 * Default values are defined via {@link KeYSEDPreferencesInitializer}.
 * </p>
 * @author Martin Hentschel
 * @see KeYSEDPreferencesInitializer.
 */
public class KeYSEDPreferences {
   /**
    * Preference key for the maximal number of set nodes per branch on run.
    */
   public static final String MAXIMAL_NUMBER_OF_SET_NODES_PER_BRANCH_ON_RUN = "org.key_project.sed.key.core.preference.maximalNumberOfSetNodesPerBranchOnRun";

   /**
    * Preference key to show method return values in debug nodes.
    */
   public static final String SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES = "org.key_project.sed.key.core.preference.showMethodReturnValuesInDebugNodes";

   /**
    * Preference key to define if KeY's main window should be shown or not.
    */
   public static final String SHOW_KEY_MAIN_WINDOW = "org.key_project.sed.key.core.preference.showKeYMainWindow";
   
   /**
    * Returns the managed {@link IPreferenceStore}.
    * @return The managed {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the maximal number of set nodes per branch on run.
    * @return The maximal number of set nodes per branch on run.
    */
   public static int getMaximalNumberOfSetNodesPerBranchOnRun() {
      return getStore().getInt(MAXIMAL_NUMBER_OF_SET_NODES_PER_BRANCH_ON_RUN);
   }
   
   /**
    * Returns the default maximal number of set nodes per branch on run.
    * @return The default maximal number of set nodes per branch on run.
    */
   public static int getDefaultMaximalNumberOfSetNodesPerBranchOnRun() {
      return getStore().getDefaultInt(MAXIMAL_NUMBER_OF_SET_NODES_PER_BRANCH_ON_RUN);
   }
   
   /**
    * Sets the maximal number of set nodes per branch on run.
    * @param value The maximal number of set nodes per branch on run.
    */
   public static void setMaximalNumberOfSetNodesPerBranchOnRun(int value) {
      getStore().setValue(MAXIMAL_NUMBER_OF_SET_NODES_PER_BRANCH_ON_RUN, value);
   }
   
   /**
    * Sets the default maximal number of set nodes per branch on run.
    * @param defaultValue The default maximal number of set nodes per branch on run.
    */
   public static void setDefaultMaximalNumberOfSetNodesPerBranchOnRun(int defaultValue) {
      getStore().setDefault(MAXIMAL_NUMBER_OF_SET_NODES_PER_BRANCH_ON_RUN, defaultValue);
   }
   
   /**
    * Checks if method return values are shown in debug node.
    * @return Show method return values in debug node?
    */
   public static boolean isShowMethodReturnValuesInDebugNode() {
      return getStore().getBoolean(SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES);
   }
   
   /**
    * Checks if method return values are shown in debug node by default.
    * @return Show method return values in debug node by default?
    */
   public static boolean isDefaultShowMethodReturnValuesInDebugNode() {
      return getStore().getDefaultBoolean(SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES);
   }
   
   /**
    * Sets if method return values are shown in debug node.
    * @param value Show method return values in debug node?
    */
   public static void setShowMethodReturnValuesInDebugNode(boolean value) {
      getStore().setValue(SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, value);
   }
   
   /**
    * Sets if method return values are shown in debug node by default.
    * @param defaultValue Show method return values in debug node by default?
    */
   public static void setDefaultShowMethodReturnValuesInDebugNode(boolean defaultValue) {
      getStore().setDefault(SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, defaultValue);
   }
   
   /**
    * Checks if KeY's main window should be shown or not.
    * @return Show or hide KeY's main window.
    */
   public static boolean isShowKeYMainWindow() {
      return getStore().getBoolean(SHOW_KEY_MAIN_WINDOW);
   }
   
   /**
    * Checks if KeY's main window should be shown or not by default.
    * @return Show or hide KeY's main window.
    */
   public static boolean isDefaultShowKeYMainWindow() {
      return getStore().getDefaultBoolean(SHOW_KEY_MAIN_WINDOW);
   }
   
   /**
    * Sets if KeY's main window should be shown or not.
    * @param value Show or hide KeY's main window.
    */
   public static void setShowKeYMainWindow(boolean value) {
      getStore().setValue(SHOW_KEY_MAIN_WINDOW, value);
   }
   
   /**
    * Sets if KeY's main window should be shown or not by default.
    * @param defaultValue Show or hide KeY's main window.
    */
   public static void setDefaultShowKeYMainWindow(boolean defaultValue) {
      getStore().setDefault(SHOW_KEY_MAIN_WINDOW, defaultValue);
   }
}
