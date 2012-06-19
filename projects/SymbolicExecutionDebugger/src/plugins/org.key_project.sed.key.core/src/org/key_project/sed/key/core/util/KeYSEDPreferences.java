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
}
