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

package org.key_project.sed.ui.visualization.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.sed.ui.visualization.Activator;

/**
 * <p>
 * Provides access to the preferences of the Symbolic Execution Debugger visualization.
 * </p>
 * <p>
 * Default values are defined via {@link VisualizationPreferencesInitializer}.
 * </p>
 * @author Martin Hentschel
 * @see KeYSEDPreferencesInitializer.
 */
public class VisualizationPreferences {
   /**
    * Preference key for the maximal number of set nodes per branch on run.
    */
   public static final String SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE = "org.key_project.sed.ui.visualization.preference.switchToStateVisualizationPerspective";

   /**
    * Returns the managed {@link IPreferenceStore}.
    * @return The managed {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the property which defines the behavior when a switch to the state visualization perspective is requested.
    * @return The property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static String getSwitchToStateVisualizationPerspective() {
      return getStore().getString(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE);
   }
   
   /**
    * Returns the default property which defines the behavior when a switch to the state visualization perspective is requested.
    * @return The default property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static String getDefaultSwitchToStateVisualizationPerspective() {
      return getStore().getDefaultString(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the state visualization perspective is requested.
    * @param value The property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static void setSwitchToStateVisualizationPerspective(String value) {
      getStore().setValue(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE, value);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the state visualization perspective is requested.
    * @param defaultValue The default property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static void setDefaultSwitchToStateVisualizationPerspective(String defaultValue) {
      getStore().setDefault(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE, defaultValue);
   }
}