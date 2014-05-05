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

package org.key_project.sed.ui.visualization.object_diagram.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.object_diagram.wizard.CreateStateWizard;
import org.key_project.util.java.StringUtil;

/**
 * {@link WizardPage} to define the initial values of new {@link ODState}s.
 * @author Martin Hentschel
 * @see CreateStateWizard
 */
public class CreateStateWizardPage extends WizardPage {
   /**
    * Input field for the name.
    */
   private Text nameText;
   
   /**
    * Constructor.
    * @param pageName The name of this page.
    */
   public CreateStateWizardPage(String pageName) {
      super(pageName);
      setTitle("Create State");
      setDescription("Define the properties of the State to create.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Create root
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(2, false));
      setControl(root);
      // Create name 
      Label nameLabel = new Label(root, SWT.NONE);
      nameLabel.setText("&Name");
      nameText = new Text(root, SWT.BORDER);
      nameText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      nameText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageCompleted();
         }
      });
      // Update page completed
      updatePageCompleted();
   }

   /**
    * Updates the page completed status.
    */
   protected void updatePageCompleted() {
      // Compute page completed status
      boolean valid = !StringUtil.isTrimmedEmpty(getNameValue());
      if (!valid) {
         setErrorMessage("No name defined.");
      }
      // Update page completed status
      setPageComplete(valid);
      if (valid) {
         setErrorMessage(null);
      }
   }

   /**
    * Returns the defined name.
    * @return The defined name.
    */
   public String getNameValue() {
      return nameText.getText();
   }
}