/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package org.key_project.sed.ui.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.sed.ui.Activator;

/**
 * Provides utility methods to edit the SED UI preferences.
 * @author Martin Hentschel
 */
public final class SEDUIPreferenceUtil {
   /**
    * Property that indicates to show all constraints.
    */
   public static final String PROP_SHOW_ALL_CONSTRAINTS = "org.key_project.sed.ui.preference.showAllConstraints";

   /**
    * Forbid instances.
    */
   private SEDUIPreferenceUtil() {
   }
   
   /**
    * Returns the {@link IPreferenceStore} to edit.
    * @return The used {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the current value of property {@link #PROP_SHOW_ALL_CONSTRAINTS}.
    * @return The current value of property{@link #PROP_SHOW_ALL_CONSTRAINTS}.
    */
   public static boolean isShowAllConstraints() {
      return getStore().getBoolean(PROP_SHOW_ALL_CONSTRAINTS);
   }
   
   /**
    * Returns the default value of property {@link #PROP_SHOW_ALL_CONSTRAINTS}.
    * @return The default value of property{@link #PROP_SHOW_ALL_CONSTRAINTS}.
    */
   public static boolean isDefaultShowAllConstraints() {
      return getStore().getDefaultBoolean(PROP_SHOW_ALL_CONSTRAINTS);
   }
   
   /**
    * Sets the current value of property {@link #PROP_SHOW_ALL_CONSTRAINTS}.
    * @param showCompactExecutionTree The new value to set.
    */
   public static void setShowAllConstraints(boolean showCompactExecutionTree) {
      getStore().setValue(PROP_SHOW_ALL_CONSTRAINTS, showCompactExecutionTree);
   }
   
   /**
    * Sets the default value of property {@link #PROP_SHOW_ALL_CONSTRAINTS}.
    * @param showCompactExecutionTree The new value to set.
    */
   public static void setDefaultShowAllConstraints(boolean showCompactExecutionTree) {
      getStore().setDefault(PROP_SHOW_ALL_CONSTRAINTS, showCompactExecutionTree);
   }
}