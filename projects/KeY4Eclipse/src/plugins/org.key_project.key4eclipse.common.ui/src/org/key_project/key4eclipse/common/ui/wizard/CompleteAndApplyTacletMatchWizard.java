package org.key_project.key4eclipse.common.ui.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.common.ui.util.EclipseUserInterfaceCustomization;
import org.key_project.key4eclipse.common.ui.wizard.page.CompleteAndApplyTacletMatchWizardPage;

import de.uka.ilkd.key.gui.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.ui.CustomUserInterface.IUserInterfaceCustomization;

/**
 * The {@link Wizard} used in {@link EclipseUserInterfaceCustomization} to
 * treat {@link IUserInterfaceCustomization#completeAndApplyTacletMatch(ApplyTacletDialogModel[], Goal)}.
 * @author Martin Hentschel
 */
public class CompleteAndApplyTacletMatchWizard extends Wizard {
   /**
    * The partial models with all different possible instantiations found automatically.
    */
   private final ApplyTacletDialogModel[] models; 
   
   /**
    * The Goal where to apply.
    */
   private final Goal goal;
   
   /**
    * The used {@link CompleteAndApplyTacletMatchWizardPage}.
    */
   private CompleteAndApplyTacletMatchWizardPage completePage;

   /**
    * Constructor.
    * @param models The partial models with all different possible instantiations found automatically.
    * @param goal The Goal where to apply.
    */
   public CompleteAndApplyTacletMatchWizard(ApplyTacletDialogModel[] models, Goal goal) {
      this.models = models;
      this.goal = goal;
      setWindowTitle("Choose Taclet Instantiation");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      completePage = new CompleteAndApplyTacletMatchWizardPage("completePage", models, goal);
      addPage(completePage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      return true;
   }
   
   /**
    * Opens the {@link CompleteAndApplyTacletMatchWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param models The partial models with all different possible instantiations found automatically.
    * @param goal The Goal where to apply.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, ApplyTacletDialogModel[] models, Goal goal) {
      WizardDialog dialog = new WizardDialog(parentShell, new CompleteAndApplyTacletMatchWizard(models, goal));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
