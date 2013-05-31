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

package org.key_project.sed.ui.visualization.object_diagram.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.object_diagram.wizard.page.CreateObjectWizardPage;

/**
 * Wizard to create a new {@link ODObject} with properties defined by the user.
 * @author Martin Hentschel
 */
public class CreateObjectWizard extends Wizard {
   /**
    * The used {@link CreateObjectWizardPage} to get user input.
    */
   private CreateObjectWizardPage createPage;
   
   /**
    * The created {@link ODObject}.
    */
   private ODObject createdObject;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      createPage = new CreateObjectWizardPage("createPage");
      addPage(createPage);
      setWindowTitle("Create new Object");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      createdObject = ODFactory.eINSTANCE.createODObject();
      createdObject.setName(createPage.getNameValue());
      createdObject.setType(createPage.getTypeValue());
      return true;
   }
   
   /**
    * Returns the created {@link ODObject}.
    * @return The created {@link ODObject}.
    */
   public ODObject getCreatedObject() {
      return createdObject;
   }

   /**
    * Opens the {@link CreateObjectWizard} in a {@link WizardDialog} and
    * returns the created {@link ODObject} or {@code null} if the user
    * has cancelled the wizard.
    * @param parentShell The parent {@link Shell} to use.
    * @return The created {@link ODObject} or {@code null} if the user has cancelled the wizard.
    */
   public static ODObject openWizard(Shell parentShell) {
      CreateObjectWizard wizard = new CreateObjectWizard();
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getCreatedObject();
      }
      else {
         return null;
      }
   }
}