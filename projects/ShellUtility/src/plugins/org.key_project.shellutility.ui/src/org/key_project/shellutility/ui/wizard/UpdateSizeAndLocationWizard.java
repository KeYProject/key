package org.key_project.shellutility.ui.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
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
      salPage = new UpdateSizeAndLocationWizardPage("salPage");
      addPage(salPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      shellToUpdate.setSize(salPage.getWidth(), salPage.getHeight());
      shellToUpdate.setLocation(salPage.getX(), salPage.getY());
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
