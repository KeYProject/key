/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.interactive.proving.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveProvingPreferences;

/**
 * The preference page "Proof Model Diagram -> Interactive proofing".
 * @author Martin Hentschel
 */
public class InteractiveProofingPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void createFieldEditors() {
      BooleanFieldEditor resetProofs = new BooleanFieldEditor(InteractiveProvingPreferences.PROP_RESET_PROOF_IF_NEW_OPENED, "Reset model proofs when new interactive proof starts", getFieldEditorParent());
      addField(resetProofs);
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   protected IPreferenceStore doGetPreferenceStore() {
      return InteractiveProvingPreferences.getPreferenceStore();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
      // Nothing to do.
   }
}
