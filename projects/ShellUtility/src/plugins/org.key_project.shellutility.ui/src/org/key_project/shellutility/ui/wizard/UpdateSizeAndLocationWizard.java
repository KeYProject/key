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

package org.key_project.shellutility.ui.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Shell;
import org.key_project.shellutility.ui.wizard.page.UpdateSizeAndLocationWizardPage;

/**
 * Allows to update location and size of a given {@link Shell}.
 * @author Martin Hentschel
 */
public class UpdateSizeAndLocationWizard extends Wizard {
   /**
    * The {@link Shell} to update.
    */
   private final Shell shellToUpdate;

   /**
    * The shown {@link UpdateSizeAndLocationWizardPage}.
    */
   private UpdateSizeAndLocationWizardPage salPage;
   
   /**
    * Constructor.
    * @param shellToUpdate The {@link Shell} to update.
    */
   public UpdateSizeAndLocationWizard(Shell shellToUpdate) {
      this.shellToUpdate = shellToUpdate;
      setWindowTitle("Shell Utility Wizard");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      salPage = new UpdateSizeAndLocationWizardPage("salPage", shellToUpdate);
      addPage(salPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      // Update size
      shellToUpdate.setSize(salPage.getWidth(), salPage.getHeight());
      // Update location
      int x = salPage.getX();
      int y = salPage.getY();
      Rectangle clientArea = getShell().getDisplay().getClientArea();
      switch (salPage.getLocation()) {
         case TOP_LEFT : x = 0;
                         y = 0;
                         break;
         case TOP_RIGHT : x = clientArea.width - shellToUpdate.getSize().x;
                          y = 0;
                          break;
         case BOTTOM_LEFT : x = 0;
                            y = clientArea.height - shellToUpdate.getSize().y;
                            break;
         case BOTTOM_RIGHT : x = clientArea.width - shellToUpdate.getSize().x;
                             y = clientArea.height - shellToUpdate.getSize().y;
                             break;
      }
      shellToUpdate.setLocation(x, y);
      return true;
   }
   
   /**
    * Opens the {@link Wizard}.
    * @param shellToUpdate The {@link Shell} to update.
    * @return The {@link Wizard} result.
    */
   public static int openWizard(Shell shellToUpdate) {
      UpdateSizeAndLocationWizard wizard = new UpdateSizeAndLocationWizard(shellToUpdate);
      WizardDialog dialog = new WizardDialog(shellToUpdate, wizard);
      return dialog.open();
   }
}