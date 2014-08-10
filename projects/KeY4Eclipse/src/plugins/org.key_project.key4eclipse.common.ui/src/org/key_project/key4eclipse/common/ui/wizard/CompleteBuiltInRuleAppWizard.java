package org.key_project.key4eclipse.common.ui.wizard;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.common.ui.completion.IInteractiveRuleApplicationCompletionPerform;
import org.key_project.key4eclipse.common.ui.util.EclipseUserInterfaceCustomization;
import org.key_project.key4eclipse.common.ui.wizard.page.CompleteBuiltInRuleAppWizardPage;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.ui.CustomUserInterface.IUserInterfaceCustomization;

/**
 * The {@link Wizard} used in {@link EclipseUserInterfaceCustomization} to
 * treat {@link IUserInterfaceCustomization#completeBuiltInRuleApp(IBuiltInRuleApp, Goal, boolean)}.
 * @author Martin Hentschel
 */
public class CompleteBuiltInRuleAppWizard extends Wizard {
   /**
    * The {@link IInteractiveRuleApplicationCompletionPerform} to use.
    */
   private final IInteractiveRuleApplicationCompletionPerform perform;
   
   /**
    * The used {@link CompleteBuiltInRuleAppWizardPage}.
    */
   private CompleteBuiltInRuleAppWizardPage completePage;
   
   /**
    * The resulting {@link IBuiltInRuleApp} computed in {@link #performFinish()}.
    */
   private IBuiltInRuleApp result;

   /**
    * Constructor.
    * @param perform The {@link IInteractiveRuleApplicationCompletionPerform} to use. 
    */
   public CompleteBuiltInRuleAppWizard(IInteractiveRuleApplicationCompletionPerform perform) {
      Assert.isNotNull(perform);
      this.perform = perform;
      setWindowTitle(perform.getWindowTitle());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      completePage = new CompleteBuiltInRuleAppWizardPage("completePage", perform);
      addPage(completePage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      result = perform.finish();
      return true;
   }

   /**
    * Returns the resulting {@link IBuiltInRuleApp}.
    * @return The resulting {@link IBuiltInRuleApp}.
    */
   public IBuiltInRuleApp getResult() {
      return result;
   }
   
   /**
    * Opens the {@link CompleteBuiltInRuleAppWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param perform The {@link IInteractiveRuleApplicationCompletionPerform} to use. 
    * @return The {@link IBuiltInRuleApp} as result.
    */
   public static IBuiltInRuleApp openWizard(Shell parentShell, IInteractiveRuleApplicationCompletionPerform perform) {
      CompleteBuiltInRuleAppWizard wizard = new CompleteBuiltInRuleAppWizard(perform);
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getResult();
      }
      else {
         return null;
      }
   }
}
