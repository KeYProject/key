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
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.object_diagram.wizard.page.CreateStateWizardPage;

/**
 * Wizard to create a new {@link ODState} with properties defined by the user.
 * @author Martin Hentschel
 */
public class CreateStateWizard extends Wizard {
   /**
    * The used {@link CreateStateWizardPage} to get user input.
    */
   private CreateStateWizardPage createPage;
   
   /**
    * The created {@link ODState}.
    */
   private ODState createdState;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      createPage = new CreateStateWizardPage("createPage");
      addPage(createPage);
      setWindowTitle("Create new State");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      createdState = ODFactory.eINSTANCE.createODState();
      createdState.setName(createPage.getNameValue());
      return true;
   }
   
   /**
    * Returns the created {@link ODState}.
    * @return The created {@link ODState}.
    */
   public ODState getCreatedState() {
      return createdState;
   }

   /**
    * Opens the {@link CreateStateWizard} in a {@link WizardDialog} and
    * returns the created {@link ODState} or {@code null} if the user
    * has cancelled the wizard.
    * @param parentShell The parent {@link Shell} to use.
    * @return The created {@link ODState} or {@code null} if the user has cancelled the wizard.
    */
   public static ODState openWizard(Shell parentShell) {
      CreateStateWizard wizard = new CreateStateWizard();
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getCreatedState();
      }
      else {
         return null;
      }
   }
}