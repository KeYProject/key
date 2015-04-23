package org.key_project.util.eclipse.swt;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;

/**
 * An extended {@link WizardDialog} which allows to customize the {@link Button}s.
 * @author Martin Hentschel
 */
public class CustomWizardDialog extends WizardDialog {
   /**
    * The text of the approve {@link Button}.
    */
   private final String approveButtonText;
   
   /**
    * Is the approve {@link Button} visible?
    */
   private final boolean approveButtonVisible;
   
   /**
    * Constructor.
    * @param parentShell The parent {@link Shell}.
    * @param newWizard The {@link IWizard} to show.
    * @param approveButtonText The text of the approve {@link Button}.
    * @param approveButtonVisible Is the approve {@link Button} visible?
    */
   public CustomWizardDialog(Shell parentShell, 
                             IWizard newWizard, 
                             String approveButtonText, 
                             boolean approveButtonVisible) {
      super(parentShell, newWizard);
      this.approveButtonText = approveButtonText;
      this.approveButtonVisible = approveButtonVisible;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Button createButton(Composite parent, int id, String label, boolean defaultButton) {
      Button button = super.createButton(parent, id, label, defaultButton);
      if (IDialogConstants.FINISH_ID == id) {
         SWTUtil.setText(button, approveButtonText);
         if (!approveButtonVisible) {
            button.setVisible(false);
         }
      }
      return button;
   }
}
