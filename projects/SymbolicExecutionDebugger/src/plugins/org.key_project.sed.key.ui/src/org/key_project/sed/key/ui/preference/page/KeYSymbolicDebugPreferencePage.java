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

package org.key_project.sed.key.ui.preference.page;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.sed.key.core.util.KeYSEDPreferences;

/**
 * Preference page for the Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYSymbolicDebugPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public KeYSymbolicDebugPreferencePage() {
      super(GRID);
      setPreferenceStore(KeYSEDPreferences.getStore());
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
      IntegerFieldEditor runSetNodes = new IntegerFieldEditor(KeYSEDPreferences.MAXIMAL_NUMBER_OF_SET_NODES_PER_BRANCH_ON_RUN, "&Maximal number of symbolic execution tree nodes per branch on run", getFieldEditorParent());
      runSetNodes.setValidRange(1, Integer.MAX_VALUE);
      addField(runSetNodes);
   }
}