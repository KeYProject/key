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

package de.hentschel.visualdbc.interactive.proving.ui.util;

import org.eclipse.jface.preference.IPreferenceStore;

import de.hentschel.visualdbc.interactive.proving.ui.Activator;
import de.hentschel.visualdbc.interactive.proving.ui.preference.InteractiveProofingPreferencePage;

/**
 * <p>
 * Provides static methods and constant to access the interactive proving preferences.
 * </p>
 * <p>
 * The initial values are defined via {@link InteractiveProvingPreferencesInitializer}.
 * </p>
 * <p>
 * The user can modify the values via the preference page
 * {@link InteractiveProofingPreferencePage}.
 * </p>
 * @author Martin Hentschel
 * @see InteractiveProvingPreferencesInitializer
 * @see InteractiveProofingPreferencePage
 */
public final class InteractiveProvingPreferences {
   /**
    * The property: reset model proofs when new interactive proof starts
    */
   public static final String PROP_RESET_PROOF_IF_NEW_OPENED = "de.hentschel.visualdbc.dbcmodel.diagram.custom.interactiveProofs.resetIfNewOpened";
   
   /**
    * Forbid instances.
    */
   private InteractiveProvingPreferences() {
   }

   /**
    * Returns the used {@link IPreferenceStore}.
    * @return The {@link IPreferenceStore} to use.
    */
   public static IPreferenceStore getPreferenceStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Checks if proofs should be reseted or not.
    * @return {@code true} = reset, {@code false} = don't reset.
    */
   public static boolean isResetProofIfNewOpened() {
      return getPreferenceStore().getBoolean(PROP_RESET_PROOF_IF_NEW_OPENED);
   }
   
   /**
    * Checks if proofs should be reseted by default or not.
    * @return {@code true} = reset, {@code false} = don't reset.
    */
   public static boolean isDefaultResetProofIfNewOpened() {
      return getPreferenceStore().getDefaultBoolean(PROP_RESET_PROOF_IF_NEW_OPENED);
   }
   
   /**
    * Sets the reset proof value value.
    * @param useCustomLayout The value to set.
    */
   public static void setResetProofIfNewOpened(boolean useCustomLayout) {
      getPreferenceStore().setValue(PROP_RESET_PROOF_IF_NEW_OPENED, useCustomLayout);
   }
   
   /**
    * Sets the default reset proof value value.
    * @param defaultUseCustomLayout The default value to set.
    */
   public static void setDefaultResetProofIfNewOpened(boolean defaultUseCustomLayout) {
      getPreferenceStore().setDefault(PROP_RESET_PROOF_IF_NEW_OPENED, defaultUseCustomLayout);
   }
}