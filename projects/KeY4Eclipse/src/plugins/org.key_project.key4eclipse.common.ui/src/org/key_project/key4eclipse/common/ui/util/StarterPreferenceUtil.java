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
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;

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
}