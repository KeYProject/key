/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.common.ui.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.key4eclipse.common.ui.Activator;
import org.key_project.key4eclipse.common.ui.starter.IFileStarter;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;
import org.key_project.key4eclipse.common.ui.starter.IProofStarter;

/**
 * Provides utility methods to edit the starter preferences.
 * @author Martin Hentschel
 */
public final class StarterPreferenceUtil {
   /**
    * Property which stores the ID of the selected {@link IGlobalStarter}.
    */
   public static final String SELECTED_GLOBAL_STARTER_ID = "org.key_project.key4eclipse.common.ui.selectedGlobalStarterID";

   /**
    * Property that indicates not to ask for an {@link IGlobalStarter} and to use the selected {@link IGlobalStarter} instead.
    */
   public static final String DONT_ASK_FOR_GLOBAL_STARTER = "org.key_project.key4eclipse.common.ui.dontAskForGlobalStarter";

   /**
    * Property that indicates that the global start functionality is disabled or enabled.
    */
   public static final String GLOBAL_STARTER_DISABLED = "org.key_project.key4eclipse.common.ui.globalStarterDisabled";
   
   /**
    * Property which stores the ID of the selected {@link IMethodStarter}.
    */
   public static final String SELECTED_METHOD_STARTER_ID = "org.key_project.key4eclipse.common.ui.selectedMethodStarterID";

   /**
    * Property that indicates not to ask for an {@link IMethodStarter} and to use the selected {@link IMethodStarter} instead.
    */
   public static final String DONT_ASK_FOR_METHOD_STARTER = "org.key_project.key4eclipse.common.ui.dontAskForMethodStarter";

   /**
    * Property that indicates that the method start functionality is disabled or enabled.
    */
   public static final String METHOD_STARTER_DISABLED = "org.key_project.key4eclipse.common.ui.methodStarterDisabled";
   
   /**
    * Property which stores the ID of the selected {@link IFileStarter}.
    */
   public static final String SELECTED_FILE_STARTER_ID = "org.key_project.key4eclipse.common.ui.selectedFileStarterID";

   /**
    * Property that indicates not to ask for an {@link IFileStarter} and to use the selected {@link IFileStarter} instead.
    */
   public static final String DONT_ASK_FOR_FILE_STARTER = "org.key_project.key4eclipse.common.ui.dontAskForFileStarter";

   /**
    * Property that indicates that the file start functionality is disabled or enabled.
    */
   public static final String FILE_STARTER_DISABLED = "org.key_project.key4eclipse.common.ui.fileStarterDisabled";
   
   /**
    * Property which stores the ID of the selected {@link IProjectStarter}.
    */
   public static final String SELECTED_PROJECT_STARTER_ID = "org.key_project.key4eclipse.common.ui.selectedProjectStarterID";

   /**
    * Property that indicates not to ask for an {@link IProjectStarter} and to use the selected {@link IProjectStarter} instead.
    */
   public static final String DONT_ASK_FOR_PROJECT_STARTER = "org.key_project.key4eclipse.common.ui.dontAskForProjectStarter";

   /**
    * Property that indicates that the project start functionality is disabled or enabled.
    */
   public static final String PROJECT_STARTER_DISABLED = "org.key_project.key4eclipse.common.ui.projectStarterDisabled";

   /**
    * Property which stores the ID of the selected {@link IProofStarter}.
    */
   public static final String SELECTED_PROOF_STARTER_ID = "org.key_project.key4eclipse.common.ui.selectedProofStarterID";

   /**
    * Property that indicates not to ask for an {@link IProofStarter} and to use the selected {@link IProofStarter} instead.
    */
   public static final String DONT_ASK_FOR_PROOF_STARTER = "org.key_project.key4eclipse.common.ui.dontAskForProofStarter";

   /**
    * Property that indicates that the project start functionality is disabled or enabled.
    */
   public static final String PROOF_STARTER_DISABLED = "org.key_project.key4eclipse.common.ui.proofStarterDisabled";
   
   /**
    * Forbid instances.
    */
   private StarterPreferenceUtil() {
   }
   
   /**
    * Returns the {@link IPreferenceStore} to edit.
    * @return The used {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   
   
   /**
    * Returns the current value of property {@link #SELECTED_GLOBAL_STARTER_ID}.
    * @return The current value of property{@link #SELECTED_GLOBAL_STARTER_ID}.
    */
   public static String getSelectedGlobalStarterID() {
      return getStore().getString(SELECTED_GLOBAL_STARTER_ID);
   }
   
   /**
    * Returns the default value of property {@link #SELECTED_GLOBAL_STARTER_ID}.
    * @return The default value of property{@link #SELECTED_GLOBAL_STARTER_ID}.
    */
   public static String getDefaultSelectedGlobalStarterID() {
      return getStore().getDefaultString(SELECTED_GLOBAL_STARTER_ID);
   }
   
   /**
    * Sets the current value of property {@link #SELECTED_GLOBAL_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setSelectedGlobalStarterID(String selectedGlobalStarterId) {
      getStore().setValue(SELECTED_GLOBAL_STARTER_ID, selectedGlobalStarterId);
   }
   
   /**
    * Sets the default value of property {@link #SELECTED_GLOBAL_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setDefaultSelectedGlobalStarterID(String selectedGlobalStarterId) {
      getStore().setDefault(SELECTED_GLOBAL_STARTER_ID, selectedGlobalStarterId);
   }
   

   
   /**
    * Returns the current value of property {@link #DONT_ASK_FOR_GLOBAL_STARTER}.
    * @return The current value of property{@link #DONT_ASK_FOR_GLOBAL_STARTER}.
    */
   public static boolean isDontAskForGlobalStarter() {
      return getStore().getBoolean(DONT_ASK_FOR_GLOBAL_STARTER);
   }
   
   /**
    * Returns the default value of property {@link #DONT_ASK_FOR_GLOBAL_STARTER}.
    * @return The default value of property{@link #DONT_ASK_FOR_GLOBAL_STARTER}.
    */
   public static boolean isDefaultDontAskForGlobalStarter() {
      return getStore().getDefaultBoolean(DONT_ASK_FOR_GLOBAL_STARTER);
   }
   
   /**
    * Sets the current value of property {@link #DONT_ASK_FOR_GLOBAL_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDontAskForGlobalStarter(boolean dontAsk) {
      getStore().setValue(DONT_ASK_FOR_GLOBAL_STARTER, dontAsk);
   }
   
   /**
    * Sets the default value of property {@link #DONT_ASK_FOR_GLOBAL_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDefaultDontAskForGlobalStarter(boolean dontAsk) {
      getStore().setDefault(DONT_ASK_FOR_GLOBAL_STARTER, dontAsk);
   }
   

   
   /**
    * Returns the current value of property {@link #GLOBAL_STARTER_DISABLED}.
    * @return The current value of property{@link #GLOBAL_STARTER_DISABLED}.
    */
   public static boolean isGlobalStarterDisabled() {
      return getStore().getBoolean(GLOBAL_STARTER_DISABLED);
   }
   
   /**
    * Returns the default value of property {@link #GLOBAL_STARTER_DISABLED}.
    * @return The default value of property{@link #GLOBAL_STARTER_DISABLED}.
    */
   public static boolean isDefaultGlobalStarterDisabled() {
      return getStore().getDefaultBoolean(GLOBAL_STARTER_DISABLED);
   }
   
   /**
    * Sets the current value of property {@link #GLOBAL_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setGlobalStarterDisabled(boolean disabled) {
      getStore().setValue(GLOBAL_STARTER_DISABLED, disabled);
   }
   
   /**
    * Sets the default value of property {@link #GLOBAL_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setDefaultGlobalStarterDisabled(boolean disabled) {
      getStore().setDefault(GLOBAL_STARTER_DISABLED, disabled);
   }
   
   
   
   /**
    * Returns the current value of property {@link #SELECTED_METHOD_STARTER_ID}.
    * @return The current value of property{@link #SELECTED_METHOD_STARTER_ID}.
    */
   public static String getSelectedMethodStarterID() {
      return getStore().getString(SELECTED_METHOD_STARTER_ID);
   }
   
   /**
    * Returns the default value of property {@link #SELECTED_METHOD_STARTER_ID}.
    * @return The default value of property{@link #SELECTED_METHOD_STARTER_ID}.
    */
   public static String getDefaultSelectedMethodStarterID() {
      return getStore().getDefaultString(SELECTED_METHOD_STARTER_ID);
   }
   
   /**
    * Sets the current value of property {@link #SELECTED_METHOD_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setSelectedMethodStarterID(String selectedGlobalStarterId) {
      getStore().setValue(SELECTED_METHOD_STARTER_ID, selectedGlobalStarterId);
   }
   
   /**
    * Sets the default value of property {@link #SELECTED_METHOD_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setDefaultSelectedMethodStarterID(String selectedGlobalStarterId) {
      getStore().setDefault(SELECTED_METHOD_STARTER_ID, selectedGlobalStarterId);
   }
   

   
   /**
    * Returns the current value of property {@link #DONT_ASK_FOR_METHOD_STARTER}.
    * @return The current value of property{@link #DONT_ASK_FOR_METHOD_STARTER}.
    */
   public static boolean isDontAskForMethodStarter() {
      return getStore().getBoolean(DONT_ASK_FOR_METHOD_STARTER);
   }
   
   /**
    * Returns the default value of property {@link #DONT_ASK_FOR_METHOD_STARTER}.
    * @return The default value of property{@link #DONT_ASK_FOR_METHOD_STARTER}.
    */
   public static boolean isDefaultDontAskForMethodStarter() {
      return getStore().getDefaultBoolean(DONT_ASK_FOR_METHOD_STARTER);
   }
   
   /**
    * Sets the current value of property {@link #DONT_ASK_FOR_METHOD_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDontAskForMethodStarter(boolean dontAsk) {
      getStore().setValue(DONT_ASK_FOR_METHOD_STARTER, dontAsk);
   }
   
   /**
    * Sets the default value of property {@link #DONT_ASK_FOR_METHOD_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDefaultDontAskForMethodStarter(boolean dontAsk) {
      getStore().setDefault(DONT_ASK_FOR_METHOD_STARTER, dontAsk);
   }
   

   
   /**
    * Returns the current value of property {@link #METHOD_STARTER_DISABLED}.
    * @return The current value of property{@link #METHOD_STARTER_DISABLED}.
    */
   public static boolean isMethodStarterDisabled() {
      return getStore().getBoolean(METHOD_STARTER_DISABLED);
   }
   
   /**
    * Returns the default value of property {@link #METHOD_STARTER_DISABLED}.
    * @return The default value of property{@link #METHOD_STARTER_DISABLED}.
    */
   public static boolean isDefaultMethodStarterDisabled() {
      return getStore().getDefaultBoolean(METHOD_STARTER_DISABLED);
   }
   
   /**
    * Sets the current value of property {@link #METHOD_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setMethodStarterDisabled(boolean disabled) {
      getStore().setValue(METHOD_STARTER_DISABLED, disabled);
   }
   
   /**
    * Sets the default value of property {@link #METHOD_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setDefaultMethodStarterDisabled(boolean disabled) {
      getStore().setDefault(METHOD_STARTER_DISABLED, disabled);
   }
   
   
   
   /**
    * Returns the current value of property {@link #SELECTED_FILE_STARTER_ID}.
    * @return The current value of property{@link #SELECTED_FILE_STARTER_ID}.
    */
   public static String getSelectedFileStarterID() {
      return getStore().getString(SELECTED_FILE_STARTER_ID);
   }
   
   /**
    * Returns the default value of property {@link #SELECTED_FILE_STARTER_ID}.
    * @return The default value of property{@link #SELECTED_FILE_STARTER_ID}.
    */
   public static String getDefaultSelectedFileStarterID() {
      return getStore().getDefaultString(SELECTED_FILE_STARTER_ID);
   }
   
   /**
    * Sets the current value of property {@link #SELECTED_FILE_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setSelectedFileStarterID(String selectedGlobalStarterId) {
      getStore().setValue(SELECTED_FILE_STARTER_ID, selectedGlobalStarterId);
   }
   
   /**
    * Sets the default value of property {@link #SELECTED_FILE_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setDefaultSelectedFileStarterID(String selectedGlobalStarterId) {
      getStore().setDefault(SELECTED_FILE_STARTER_ID, selectedGlobalStarterId);
   }
   

   
   /**
    * Returns the current value of property {@link #DONT_ASK_FOR_FILE_STARTER}.
    * @return The current value of property{@link #DONT_ASK_FOR_FILE_STARTER}.
    */
   public static boolean isDontAskForFileStarter() {
      return getStore().getBoolean(DONT_ASK_FOR_FILE_STARTER);
   }
   
   /**
    * Returns the default value of property {@link #DONT_ASK_FOR_FILE_STARTER}.
    * @return The default value of property{@link #DONT_ASK_FOR_FILE_STARTER}.
    */
   public static boolean isDefaultDontAskForFileStarter() {
      return getStore().getDefaultBoolean(DONT_ASK_FOR_FILE_STARTER);
   }
   
   /**
    * Sets the current value of property {@link #DONT_ASK_FOR_FILE_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDontAskForFileStarter(boolean dontAsk) {
      getStore().setValue(DONT_ASK_FOR_FILE_STARTER, dontAsk);
   }
   
   /**
    * Sets the default value of property {@link #DONT_ASK_FOR_FILE_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDefaultDontAskForFileStarter(boolean dontAsk) {
      getStore().setDefault(DONT_ASK_FOR_FILE_STARTER, dontAsk);
   }
   

   
   /**
    * Returns the current value of property {@link #FILE_STARTER_DISABLED}.
    * @return The current value of property{@link #FILE_STARTER_DISABLED}.
    */
   public static boolean isFileStarterDisabled() {
      return getStore().getBoolean(FILE_STARTER_DISABLED);
   }
   
   /**
    * Returns the default value of property {@link #FILE_STARTER_DISABLED}.
    * @return The default value of property{@link #FILE_STARTER_DISABLED}.
    */
   public static boolean isDefaultFileStarterDisabled() {
      return getStore().getDefaultBoolean(FILE_STARTER_DISABLED);
   }
   
   /**
    * Sets the current value of property {@link #FILE_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setFileStarterDisabled(boolean disabled) {
      getStore().setValue(FILE_STARTER_DISABLED, disabled);
   }
   
   /**
    * Sets the default value of property {@link #FILE_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setDefaultFileStarterDisabled(boolean disabled) {
      getStore().setDefault(FILE_STARTER_DISABLED, disabled);
   }
   
   
   
   /**
    * Returns the current value of property {@link #SELECTED_PROJECT_STARTER_ID}.
    * @return The current value of property{@link #SELECTED_PROJECT_STARTER_ID}.
    */
   public static String getSelectedProjectStarterID() {
      return getStore().getString(SELECTED_PROJECT_STARTER_ID);
   }
   
   /**
    * Returns the default value of property {@link #SELECTED_PROJECT_STARTER_ID}.
    * @return The default value of property{@link #SELECTED_PROJECT_STARTER_ID}.
    */
   public static String getDefaultSelectedProjectStarterID() {
      return getStore().getDefaultString(SELECTED_PROJECT_STARTER_ID);
   }
   
   /**
    * Sets the current value of property {@link #SELECTED_PROJECT_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setSelectedProjectStarterID(String selectedGlobalStarterId) {
      getStore().setValue(SELECTED_PROJECT_STARTER_ID, selectedGlobalStarterId);
   }
   
   /**
    * Sets the default value of property {@link #SELECTED_PROJECT_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setDefaultSelectedProjectStarterID(String selectedGlobalStarterId) {
      getStore().setDefault(SELECTED_PROJECT_STARTER_ID, selectedGlobalStarterId);
   }
   

   
   /**
    * Returns the current value of property {@link #DONT_ASK_FOR_PROJECT_STARTER}.
    * @return The current value of property{@link #DONT_ASK_FOR_PROJECT_STARTER}.
    */
   public static boolean isDontAskForProjectStarter() {
      return getStore().getBoolean(DONT_ASK_FOR_PROJECT_STARTER);
   }
   
   /**
    * Returns the default value of property {@link #DONT_ASK_FOR_PROJECT_STARTER}.
    * @return The default value of property{@link #DONT_ASK_FOR_PROJECT_STARTER}.
    */
   public static boolean isDefaultDontAskForProjectStarter() {
      return getStore().getDefaultBoolean(DONT_ASK_FOR_PROJECT_STARTER);
   }
   
   /**
    * Sets the current value of property {@link #DONT_ASK_FOR_PROJECT_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDontAskForProjectStarter(boolean dontAsk) {
      getStore().setValue(DONT_ASK_FOR_PROJECT_STARTER, dontAsk);
   }
   
   /**
    * Sets the default value of property {@link #DONT_ASK_FOR_PROJECT_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDefaultDontAskForProjectStarter(boolean dontAsk) {
      getStore().setDefault(DONT_ASK_FOR_PROJECT_STARTER, dontAsk);
   }
   

   
   /**
    * Returns the current value of property {@link #PROJECT_STARTER_DISABLED}.
    * @return The current value of property{@link #PROJECT_STARTER_DISABLED}.
    */
   public static boolean isProjectStarterDisabled() {
      return getStore().getBoolean(PROJECT_STARTER_DISABLED);
   }
   
   /**
    * Returns the default value of property {@link #PROJECT_STARTER_DISABLED}.
    * @return The default value of property{@link #PROJECT_STARTER_DISABLED}.
    */
   public static boolean isDefaultProjectStarterDisabled() {
      return getStore().getDefaultBoolean(PROJECT_STARTER_DISABLED);
   }
   
   /**
    * Sets the current value of property {@link #PROJECT_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setProjectStarterDisabled(boolean disabled) {
      getStore().setValue(PROJECT_STARTER_DISABLED, disabled);
   }
   
   /**
    * Sets the default value of property {@link #PROJECT_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setDefaultProjectStarterDisabled(boolean disabled) {
      getStore().setDefault(PROJECT_STARTER_DISABLED, disabled);
   }
   
   
   
   /**
    * Returns the current value of property {@link #SELECTED_PROOF_STARTER_ID}.
    * @return The current value of property{@link #SELECTED_PROOF_STARTER_ID}.
    */
   public static String getSelectedProofStarterID() {
      return getStore().getString(SELECTED_PROOF_STARTER_ID);
   }
   
   /**
    * Returns the default value of property {@link #SELECTED_PROOF_STARTER_ID}.
    * @return The default value of property{@link #SELECTED_PROOF_STARTER_ID}.
    */
   public static String getDefaultSelectedProofStarterID() {
      return getStore().getDefaultString(SELECTED_PROOF_STARTER_ID);
   }
   
   /**
    * Sets the current value of property {@link #SELECTED_PROOF_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setSelectedProofStarterID(String selectedGlobalStarterId) {
      getStore().setValue(SELECTED_PROOF_STARTER_ID, selectedGlobalStarterId);
   }
   
   /**
    * Sets the default value of property {@link #SELECTED_PROOF_STARTER_ID}.
    * @param selectedGlobalStarterId The new value to set.
    */
   public static void setDefaultSelectedProofStarterID(String selectedGlobalStarterId) {
      getStore().setDefault(SELECTED_PROOF_STARTER_ID, selectedGlobalStarterId);
   }
   

   
   /**
    * Returns the current value of property {@link #DONT_ASK_FOR_PROOF_STARTER}.
    * @return The current value of property{@link #DONT_ASK_FOR_PROOF_STARTER}.
    */
   public static boolean isDontAskForProofStarter() {
      return getStore().getBoolean(DONT_ASK_FOR_PROOF_STARTER);
   }
   
   /**
    * Returns the default value of property {@link #DONT_ASK_FOR_PROOF_STARTER}.
    * @return The default value of property{@link #DONT_ASK_FOR_PROOF_STARTER}.
    */
   public static boolean isDefaultDontAskForProofStarter() {
      return getStore().getDefaultBoolean(DONT_ASK_FOR_PROOF_STARTER);
   }
   
   /**
    * Sets the current value of property {@link #DONT_ASK_FOR_PROOF_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDontAskForProofStarter(boolean dontAsk) {
      getStore().setValue(DONT_ASK_FOR_PROOF_STARTER, dontAsk);
   }
   
   /**
    * Sets the default value of property {@link #DONT_ASK_FOR_PROOF_STARTER}.
    * @param dontAsk The new value to set.
    */
   public static void setDefaultDontAskForProofStarter(boolean dontAsk) {
      getStore().setDefault(DONT_ASK_FOR_PROOF_STARTER, dontAsk);
   }
   

   
   /**
    * Returns the current value of property {@link #PROOF_STARTER_DISABLED}.
    * @return The current value of property{@link #PROOF_STARTER_DISABLED}.
    */
   public static boolean isProofStarterDisabled() {
      return getStore().getBoolean(PROOF_STARTER_DISABLED);
   }
   
   /**
    * Returns the default value of property {@link #PROOF_STARTER_DISABLED}.
    * @return The default value of property{@link #PROOF_STARTER_DISABLED}.
    */
   public static boolean isDefaultProofStarterDisabled() {
      return getStore().getDefaultBoolean(PROOF_STARTER_DISABLED);
   }
   
   /**
    * Sets the current value of property {@link #PROOF_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setProofStarterDisabled(boolean disabled) {
      getStore().setValue(PROOF_STARTER_DISABLED, disabled);
   }
   
   /**
    * Sets the default value of property {@link #PROOF_STARTER_DISABLED}.
    * @param disabled The new value to set.
    */
   public static void setDefaultProofStarterDisabled(boolean disabled) {
      getStore().setDefault(PROOF_STARTER_DISABLED, disabled);
   }
}