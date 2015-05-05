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
    * The modified or created profile.
    */
   private IEditableDerivedProfile modifiedProfile;

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
      modifiedProfile = profilePage.performFinish();
      return modifiedProfile != null;
   }
   
   /**
    * Returns the modified or created profile.
    * @return The modified or created profile.
    */
   public IEditableDerivedProfile getModifiedProfile() {
      return modifiedProfile;
   }

   /**
    * Opens the {@link JMLProfileWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param profile The {@link IJMLProfile} to edit.
    * @return The modified or created profile.
    */
   public static IEditableDerivedProfile openWizard(Shell parentShell, 
                                                    IJMLProfile profile) {
      JMLProfileWizard wizard = new JMLProfileWizard(profile);
      WizardDialog dialog = new CustomWizardDialog(parentShell, 
                                                   wizard, 
                                                   IDialogConstants.OK_LABEL, 
                                                   profile == null || profile instanceof IEditableDerivedProfile);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getModifiedProfile();
      }
      else {
         return null;
      }
   }
}
