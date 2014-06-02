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

package org.key_project.sed.ui.visualization.execution_tree.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;

/**
 * {@link WizardPage} to define which information will be saved in a SET file.
 * @author Martin Hentschel
 */
public class ModelFileSaveOptionsWizardPage extends WizardPage {
   /**
    * Defines if variables will be saved or not.
    */
   private Button saveVariablesButton;
   
   /**
    * Defines if call stack will be saved or not.
    */
   private Button saveCallStackButton;

   /**
    * Constructor.
     * @param pageName The name of the page
    */
   public ModelFileSaveOptionsWizardPage(String pageName) {
      super(pageName);
      setTitle("Save Symbolic Execution Tree Domain Model Options");
      setDescription("Define which information will be saved.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      setControl(root);
      root.setLayout(new GridLayout(1, false));
      saveVariablesButton = new Button(root, SWT.CHECK);
      saveVariablesButton.setText("Save &variables");
      saveCallStackButton = new Button(root, SWT.CHECK);
      saveCallStackButton.setText("Save call &stack");
   }
   
   /**
    * Checks if variables should be saved.
    * @return {@code true} save variables, {@code false} do not save variables.
    */
   public boolean isSaveVariables() {
      return saveVariablesButton.getSelection();
   }
   
   /**
    * Checks if call stack should be saved.
    * @return {@code true} save call stack, {@code false} do not save call stack.
    */
   public boolean isSaveCallStack() {
      return saveCallStackButton.getSelection();
   }
}