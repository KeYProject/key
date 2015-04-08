package org.key_project.jmlediting.ui.wizard;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.ui.wizard.page.JMLProfileWizardPage;
import org.key_project.util.eclipse.swt.CustomWizardDialog;

/**
 * Wizard o edit {@link IJMLProfile}s.
 * @author Martin Hentschel
 */
public class JMLProfileWizard extends Wizard {
   /**
    * The shown {@link JMLProfileWizardPage}.
    */
   private final JMLProfileWizardPage profilePage;

   /**
    * Constructor.
    * @param profile Optionally, the existing {@link IJMLProfile} to show/edit.
    */
   public JMLProfileWizard(IJMLProfile profile) {
      this.profilePage = new JMLProfileWizardPage("profilePage", profile);
      setHelpAvailable(false);
      setWindowTitle(profilePage.getTitle());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      addPage(profilePage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      return profilePage.performFinish();
   }
   
   /**
    * Opens the {@link JMLProfileWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param profile The {@link IJMLProfile} to edit.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, 
                                final IJMLProfile profile) {
      WizardDialog dialog = new CustomWizardDialog(parentShell, 
                                                   new JMLProfileWizard(profile), 
                                                   IDialogConstants.OK_LABEL, 
                                                   profile == null || profile instanceof IEditableDerivedProfile);
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
