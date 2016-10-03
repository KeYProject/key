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

package org.key_project.keyide.ui.preference.page;

import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.keyide.ui.util.KeYIDEPreferences;

/**
 * This {@link IPreferencePage} allows to edit the KeYIDE specific color settings.
 * @author Martin Hentschel
 */
public class KeYIDEColorPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public KeYIDEColorPreferencePage() {
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
      Group proofTreeGroup = new Group(getFieldEditorParent(), SWT.NONE);
      proofTreeGroup.setText("Proof Tree");
      GridData gd = new GridData(GridData.FILL_HORIZONTAL);
      gd.horizontalSpan = 2;
      proofTreeGroup.setLayoutData(gd);
      addField(new ColorFieldEditor(KeYIDEPreferences.CLOSED_GOAL_COLOR, "Closed Goal", proofTreeGroup));
      addField(new ColorFieldEditor(KeYIDEPreferences.LINKED_GOAL_COLOR, "Linked Goal", proofTreeGroup));
      addField(new ColorFieldEditor(KeYIDEPreferences.DISABLED_GOAL_COLOR, "Disabled Goal", proofTreeGroup));
      addField(new ColorFieldEditor(KeYIDEPreferences.OPEN_GOAL_COLOR, "Open Goal", proofTreeGroup));
      addField(new ColorFieldEditor(KeYIDEPreferences.NODE_WITH_NOTES_COLOR, "Node with Notes", proofTreeGroup));
      addField(new ColorFieldEditor(KeYIDEPreferences.NODE_WITH_ACTIVE_STATEMENT_COLOR, "Node with Active Statement", proofTreeGroup));
      Group proofTreeSearchGroup = new Group(getFieldEditorParent(), SWT.NONE);
      proofTreeSearchGroup.setText("Proof Tree Search");
      proofTreeSearchGroup.setLayoutData(gd);
      addField(new ColorFieldEditor(KeYIDEPreferences.FOUND_NODE_COLOR, "Found Node", proofTreeSearchGroup));
   }
}