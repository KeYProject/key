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

import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.PreferenceDialog;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.dialogs.PreferencesUtil;
import org.key_project.sed.key.core.util.KeYSEDPreferences;

/**
 * Preference page for the colors used by KeY's SED integration.
 * @author Martin Hentschel
 */
public class KeYColorsPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * The ID of this preference page.
    */
   public static final String ID = "org.key_project.sed.ui.preference.page.colors";
   
   /**
    * Constructor
    */
   public KeYColorsPreferencePage() {
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
      Group group = new Group(getFieldEditorParent(), SWT.NONE);
      group.setText("Truth Value Tracing");
      group.setLayout(new GridLayout(2, false));
      group.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      ColorFieldEditor trueColor = new ColorFieldEditor(KeYSEDPreferences.TRUTH_VALUE_TRACING_TRUE, "True", group);
      addField(trueColor);
      ColorFieldEditor falseColor = new ColorFieldEditor(KeYSEDPreferences.TRUTH_VALUE_TRACING_FALSE, "False", group);
      addField(falseColor);
      ColorFieldEditor unknownColor = new ColorFieldEditor(KeYSEDPreferences.TRUTH_VALUE_TRACING_UNKNOWN, "Unknown", group);
      addField(unknownColor);
   }

   /**
    * Opens the {@link PreferencePage} and shows this {@link PreferencePage}.
    * @param parentShell The parent {@link Shell}.
    * @return The dialog result.
    */
   public static int openPreferencePage(Shell parentShell) {
      PreferenceDialog dialog = PreferencesUtil.createPreferenceDialogOn(parentShell, ID, null, null);
      if (dialog != null) {
         return dialog.open();
      }
      else {
         return PreferenceDialog.CANCEL;
      }
   }
}