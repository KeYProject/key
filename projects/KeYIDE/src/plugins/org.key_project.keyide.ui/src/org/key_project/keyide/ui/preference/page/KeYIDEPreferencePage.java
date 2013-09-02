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

package org.key_project.keyide.ui.preference.page;

import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferencePage;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.keyide.ui.util.KeYIDEPreferences;

/**
 * This {@link IPreferencePage} allows to edit the KeYIDE specific settings.
 * @author Martin Hentschel
 */
public class KeYIDEPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public KeYIDEPreferencePage() {
      super(GRID);
      setPreferenceStore(KeYIDEPreferences.getStore());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void createFieldEditors() {
      RadioGroupFieldEditor switchToStateVisualizationPerspectiveEditor = new RadioGroupFieldEditor(KeYIDEPreferences.SWITCH_TO_KEY_PERSPECTIVE, "Open the associated perspective when a KeY proof is requested", 3, new String[][] {{"Always", MessageDialogWithToggle.ALWAYS}, {"Prompt", MessageDialogWithToggle.PROMPT}, {"Never", MessageDialogWithToggle.NEVER}}, getFieldEditorParent(), true);
      addField(switchToStateVisualizationPerspectiveEditor);
   }
}