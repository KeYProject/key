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
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.wizard.CreateValueWizard;
import org.key_project.util.java.StringUtil;

/**
 * {@link WizardPage} to define the initial values of new {@link ODValue}s.
 * @author Martin Hentschel
 * @see CreateValueWizard
 */
public class CreateValueWizardPage extends WizardPage {
   /**
    * Input field for the name.
    */
   private Text nameText;
   
   /**
    * Input field for the value.
    */
   private Text valueText;
   
   /**
    * Input field for the type.
    */
   private Text typeText;
   
   /**
    * Constructor.
    * @param pageName The name of this page.
    */
   public CreateValueWizardPage(String pageName) {
      super(pageName);
      setTitle("Create Value");
      setDescription("Define the properties of the Value to create.");
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
      // Create value 
      Label valueLabel = new Label(root, SWT.NONE);
      valueLabel.setText("&Value");
      valueText = new Text(root, SWT.BORDER);
      valueText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      valueText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageCompleted();
         }
      });
      // Create type 
      Label typeLabel = new Label(root, SWT.NONE);
      typeLabel.setText("&Type");
      typeText = new Text(root, SWT.BORDER);
      typeText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      typeText.addModifyListener(new ModifyListener() {
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
      if (valid) {
         valid = !StringUtil.isTrimmedEmpty(getValueValue());
         if (!valid) {
            setErrorMessage("No value defined.");
         }
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

   /**
    * Returns the defined value.
    * @return The defined value.
    */
   public String getValueValue() {
      return valueText.getText();
   }

   /**
    * Returns the defined type.
    * @return The defined type.
    */
   public String getTypeValue() {
      return typeText.getText();
   }
}