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

package org.key_project.sed.key.ui.preference.page;

import org.eclipse.debug.internal.ui.SWTFactory;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.util.eclipse.preference.ObservableBooleanFieldEditor;
import org.key_project.util.eclipse.preference.event.FieldEditorValueEvent;
import org.key_project.util.eclipse.preference.event.IFieldEditorValueListener;

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
      final Composite spacer = SWTFactory.createComposite(group, 1, 1, GridData.FILL_HORIZONTAL);
      BooleanFieldEditor returnEdit = new BooleanFieldEditor(KeYSEDPreferences.SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, "&Show method return values in debug nodes", SWT.NONE, spacer);
      addField(returnEdit);
      BooleanFieldEditor mergeEdit = new BooleanFieldEditor(KeYSEDPreferences.MERGE_BRANCH_CONDITIONS, "&Merge branch conditions", SWT.NONE, spacer);
      addField(mergeEdit);
      final ObservableBooleanFieldEditor ppEdit = new ObservableBooleanFieldEditor(KeYSEDPreferences.USE_PRETTY_PRINTING, "Use &pretty printing", SWT.NONE, spacer);
      addField(ppEdit);
      final BooleanFieldEditor unicodeEdit = new BooleanFieldEditor(KeYSEDPreferences.USE_UNICODE, "Use &unicode symbols", SWT.NONE, spacer);
      addField(unicodeEdit);
      ppEdit.addFieldEditorValueListener(new IFieldEditorValueListener() {
         @Override
         public void shownValueChanged(FieldEditorValueEvent e) {
            unicodeEdit.setEnabled(ppEdit.getBooleanValue(), spacer);
         }
      });
      BooleanFieldEditor sigEdit = new BooleanFieldEditor(KeYSEDPreferences.SHOW_SIGNATURE_ON_METHOD_RETURN_NODES, "Show signature instead of only the name on method &return nodes", SWT.NONE, spacer);
      addField(sigEdit);

      group = SWTFactory.createGroup(getFieldEditorParent(), "Variables", 1, 1, GridData.FILL_HORIZONTAL);
      final Composite variablesSpacer = SWTFactory.createComposite(group, 2, 1, GridData.FILL_HORIZONTAL);
      final ObservableBooleanFieldEditor varEdit = new ObservableBooleanFieldEditor(KeYSEDPreferences.SHOW_VARIABLES_OF_SELECTED_DEBUG_NODE, "Show &variables of selected debug node", SWT.NONE, variablesSpacer);
      varEdit.fillIntoGrid(variablesSpacer, 2);
      addField(varEdit);
      final ComboFieldEditor variablesEditor = new ComboFieldEditor(KeYSEDPreferences.VARIABLES_ARE_COMPUTED_FROM_UPDATES, "Variables &computation", new String[][] {{"Based on visible type structure", "false"}, {"Based on sequent", "true"}}, variablesSpacer);
      addField(variablesEditor);
      varEdit.addFieldEditorValueListener(new IFieldEditorValueListener() {
         @Override
         public void shownValueChanged(FieldEditorValueEvent e) {
            variablesEditor.setEnabled(varEdit.getBooleanValue(), variablesSpacer);
         }
      });
      
      group = SWTFactory.createGroup(getFieldEditorParent(), "KeY", 1, 1, GridData.FILL_HORIZONTAL);
      Composite keySpacer = SWTFactory.createComposite(group, 1, 1, GridData.FILL_HORIZONTAL);
      BooleanFieldEditor mainWindowEdit = new BooleanFieldEditor(KeYSEDPreferences.SHOW_KEY_MAIN_WINDOW, "Show &KeY's main window (only for experienced user)", SWT.NONE, keySpacer);
      addField(mainWindowEdit);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void adjustGridLayout() {
      // Nothing to do
   }
}