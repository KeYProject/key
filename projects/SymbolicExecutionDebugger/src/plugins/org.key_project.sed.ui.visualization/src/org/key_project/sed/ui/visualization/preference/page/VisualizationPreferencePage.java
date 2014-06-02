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

package org.key_project.sed.ui.visualization.preference.page;

import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;

/**
 * Preference page for the visualization.
 * @author Martin Hentschel
 */
public class VisualizationPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public VisualizationPreferencePage() {
      super(GRID);
      setPreferenceStore(VisualizationPreferences.getStore());
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
      RadioGroupFieldEditor switchToStateVisualizationPerspectiveEditor = new RadioGroupFieldEditor(VisualizationPreferences.SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE, "Open the associated perspective when a state visualization is requested", 3, new String[][] {{"Always", MessageDialogWithToggle.ALWAYS}, {"Prompt", MessageDialogWithToggle.PROMPT}, {"Never", MessageDialogWithToggle.NEVER}}, getFieldEditorParent(), true);
      addField(switchToStateVisualizationPerspectiveEditor);
      
      Group executionTreeGroup = new Group(getFieldEditorParent(), SWT.NONE);
      executionTreeGroup.setText("Symbolic Execution Tree");
      executionTreeGroup.setLayout(new GridLayout(2, false));
      executionTreeGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      
      ColorFieldEditor nodeFirstBackgroundColor = new ColorFieldEditor(VisualizationPreferences.EXECUTION_TREE_NODE_FIRST_BACKGROUND_COLOR, "First Background Color", executionTreeGroup);
      addField(nodeFirstBackgroundColor);
      
      ColorFieldEditor nodeSecondBackgroundColor = new ColorFieldEditor(VisualizationPreferences.EXECUTION_TREE_NODE_SECOND_BACKGROUND_COLOR, "Second Background Color", executionTreeGroup);
      addField(nodeSecondBackgroundColor);
      
      ComboFieldEditor backgroundDirection = new ComboFieldEditor(VisualizationPreferences.EXECUTION_TREE_NODE_BACKGROUND_DIRECTION, "Execution Direction", new String[][] {{"Horizontal", VisualizationPreferences.EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_HORIZONTAL}, {"Vertical", VisualizationPreferences.EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_VERTICAL}}, executionTreeGroup);
      addField(backgroundDirection);
      
      ColorFieldEditor nodeForegroundColor = new ColorFieldEditor(VisualizationPreferences.EXECUTION_TREE_NODE_FOREGROUND_COLOR, "Foreground Color", executionTreeGroup);
      addField(nodeForegroundColor);
      
      ColorFieldEditor nodeTextColor = new ColorFieldEditor(VisualizationPreferences.EXECUTION_TREE_NODE_TEXT_COLOR, "Text Color", executionTreeGroup);
      addField(nodeTextColor);
      
      ColorFieldEditor nodeConnectionColor = new ColorFieldEditor(VisualizationPreferences.EXECUTION_TREE_NODE_CONNECTION_COLOR, "Connection Color", executionTreeGroup);
      addField(nodeConnectionColor);
   }
}