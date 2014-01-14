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

import org.eclipse.debug.internal.ui.SWTFactory;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.sed.key.core.util.KeYSEDPreferences;

/**
 * Preference page for the Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYLaunchSymbolicDebugPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public KeYLaunchSymbolicDebugPreferencePage() {
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
      // Group style was copied from org.eclipse.debug.internal.ui.preferences.LaunchingPreferencePage
      Group group = SWTFactory.createGroup(getFieldEditorParent(), "Symbolic Execution Tree", 1, 1, GridData.FILL_HORIZONTAL);
      Composite spacer = SWTFactory.createComposite(group, 1, 1, GridData.FILL_HORIZONTAL);
      BooleanFieldEditor edit = new BooleanFieldEditor(KeYSEDPreferences.SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, "&Show method return values in debug nodes", SWT.NONE, spacer);
      edit.fillIntoGrid(spacer, 2);
      addField(edit);
      edit = new BooleanFieldEditor(KeYSEDPreferences.SHOW_VARIABLES_OF_SELECTED_DEBUG_NODE, "Show &variables of selected debug node", SWT.NONE, spacer);
      edit.fillIntoGrid(spacer, 2);
      addField(edit);
      edit = new BooleanFieldEditor(KeYSEDPreferences.MERGE_BRANCH_CONDITIONS, "&Merge branch conditions", SWT.NONE, spacer);
      edit.fillIntoGrid(spacer, 2);
      addField(edit);
      edit = new BooleanFieldEditor(KeYSEDPreferences.USE_PRETTY_PRINTING, "Use &pretty printing", SWT.NONE, spacer);
      edit.fillIntoGrid(spacer, 2);
      addField(edit);

      group = SWTFactory.createGroup(getFieldEditorParent(), "KeY", 1, 1, GridData.FILL_HORIZONTAL);
      spacer = SWTFactory.createComposite(group, 1, 1, GridData.FILL_HORIZONTAL);
      edit = new BooleanFieldEditor(KeYSEDPreferences.SHOW_KEY_MAIN_WINDOW, "Show KeY's &main window (only for experienced user)", SWT.NONE, spacer);
      edit.fillIntoGrid(spacer, 2);
      addField(edit);
   }
}