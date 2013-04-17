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

package de.hentschel.visualdbc.dbcmodel.diagram.custom.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.CustomPreferences;

/**
 * The preference page "Proof Model Diagram -> Layout".
 * @author Martin Hentschel
 */
public class DbCModelLayoutPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void createFieldEditors() {
      BooleanFieldEditor useCustomLayout = new BooleanFieldEditor(CustomPreferences.PROP_USE_CUSTOM_LAYOUT, "Use custom layout", getFieldEditorParent());
      IntegerFieldEditor verticalSpacingEditor = new IntegerFieldEditor(CustomPreferences.PROP_VERTICAL_SPACING, "Vertical spacing", getFieldEditorParent());
      verticalSpacingEditor.setValidRange(0, Integer.MAX_VALUE);
      addField(useCustomLayout);
      addField(verticalSpacingEditor);
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   protected IPreferenceStore doGetPreferenceStore() {
      return CustomPreferences.getPreferenceStore();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
      // Nothing to do.
   }
}