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

package org.key_project.sed.ui.visualization.object_diagram.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.wizard.page.CreateValueWizardPage;

/**
 * Wizard to create a new {@link ODValue} with properties defined by the user.
 * @author Martin Hentschel
 */
public class CreateValueWizard extends Wizard {
   /**
    * The used {@link CreateValueWizardPage} to get user input.
    */
   private CreateValueWizardPage createPage;
   
   /**
    * The created {@link ODValue}.
    */
   private ODValue createdValue;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      createPage = new CreateValueWizardPage("createPage");
      addPage(createPage);
      setWindowTitle("Create new Value");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      createdValue = ODFactory.eINSTANCE.createODValue();
      createdValue.setName(createPage.getNameValue());
      createdValue.setValue(createPage.getValueValue());
      createdValue.setType(createPage.getTypeValue());
      return true;
   }
   
   /**
    * Returns the created {@link ODValue}.
    * @return The created {@link ODValue}.
    */
   public ODValue getCreatedValue() {
      return createdValue;
   }

   /**
    * Opens the {@link CreateValueWizard} in a {@link WizardDialog} and
    * returns the created {@link ODValue} or {@code null} if the user
    * has cancelled the wizard.
    * @param parentShell The parent {@link Shell} to use.
    * @return The created {@link ODValue} or {@code null} if the user has cancelled the wizard.
    */
   public static ODValue openWizard(Shell parentShell) {
      CreateValueWizard wizard = new CreateValueWizard();
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getCreatedValue();
      }
      else {
         return null;
      }
   }
}