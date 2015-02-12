package org.key_project.key4eclipse.common.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.key_project.key4eclipse.common.ui.wizard.CompleteAndApplyTacletMatchWizard;

import de.uka.ilkd.key.gui.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;

/**
 * The only {@link WizardPage} shown in a {@link CompleteAndApplyTacletMatchWizard}.
 * @author Martin Hentschel
 */
public class CompleteAndApplyTacletMatchWizardPage extends WizardPage {
   /**
    * The partial models with all different possible instantiations found automatically.
    */
   private final ApplyTacletDialogModel[] models; 
   
   /**
    * The Goal where to apply.
    */
   private final Goal goal;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param models The partial models with all different possible instantiations found automatically.
    * @param goal The Goal where to apply.
    */
   public CompleteAndApplyTacletMatchWizardPage(String pageName, ApplyTacletDialogModel[] models, Goal goal) {
      super(pageName);
      this.models = models;
      this.goal = goal;
      setTitle("Choose Taclet Instantiation");
      setDescription("Define instantiations required to apply the taclet.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Create root
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new FillLayout());
      setControl(root);
      // Create label
      Label label = new Label(root, SWT.NONE);
      label.setText("This functionality will be available soon...");
      // Set initial page complete state.
      updatePageComplete();
   }
   
   /**
    * Checks the user input for validity and updates the page complete state.
    */
   protected void updatePageComplete() {
      setPageComplete(false);
      setErrorMessage("Functionality is not available yet.");
   }
}
