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
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.object_diagram.wizard.page.CreateAssociationWizardPage;

/**
 * Wizard to create a new {@link ODAssociation} with properties defined by the user.
 * @author Martin Hentschel
 */
public class CreateAssociationWizard extends Wizard {
   /**
    * The used {@link CreateAssociationWizardPage} to get user input.
    */
   private CreateAssociationWizardPage createPage;
   
   /**
    * The created {@link ODAssociation}.
    */
   private ODAssociation createdAssociation;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      createPage = new CreateAssociationWizardPage("createPage");
      addPage(createPage);
      setWindowTitle("Create new Association");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      createdAssociation = ODFactory.eINSTANCE.createODAssociation();
      createdAssociation.setName(createPage.getNameValue());
      return true;
   }
   
   /**
    * Returns the created {@link ODAssociation}.
    * @return The created {@link ODAssociation}.
    */
   public ODAssociation getCreatedAssociation() {
      return createdAssociation;
   }

   /**
    * Opens the {@link CreateAssociationWizard} in a {@link WizardDialog} and
    * returns the created {@link ODAssociation} or {@code null} if the user
    * has cancelled the wizard.
    * @param parentShell The parent {@link Shell} to use.
    * @return The created {@link ODAssociation} or {@code null} if the user has cancelled the wizard.
    */
   public static ODAssociation openWizard(Shell parentShell) {
      CreateAssociationWizard wizard = new CreateAssociationWizard();
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getCreatedAssociation();
      }
      else {
         return null;
      }
   }
}