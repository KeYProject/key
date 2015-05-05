package org.key_project.jmlediting.ui.wizard;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.jmlediting.ui.wizard.page.JMLKeywordWizardPage;
import org.key_project.util.eclipse.swt.CustomWizardDialog;

/**
 * {@link Wizard} to edit {@link IUserDefinedKeyword}s.
 * @author Martin Hentschel
 */
public class JMLKeywordWizard extends Wizard {
   /**
    * The used {@link JMLKeywordWizardPage}.
    */
   private final JMLKeywordWizardPage keywordPage;
   
   /**
    * The created {@link IUserDefinedKeyword}.
    */
   private IUserDefinedKeyword result;

   /**
    * Constructor
    * @param derivedProfile The parent {@link IEditableDerivedProfile}.
    * @param keyword Optionally, the existing {@link IUserDefinedKeyword} to edit.
    */
   public JMLKeywordWizard(IEditableDerivedProfile derivedProfile, IUserDefinedKeyword keyword) {
      this.keywordPage = new JMLKeywordWizardPage("keywordPage", derivedProfile, keyword);
      setHelpAvailable(false);
      setWindowTitle(keywordPage.getTitle());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      addPage(keywordPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      result = keywordPage.performFinish();
      return result != null;
   }
   
   /**
    * Returns the created {@link IUserDefinedKeyword}.
    * @return The created {@link IUserDefinedKeyword}.
    */
   public IUserDefinedKeyword getResult() {
      return result;
   }

   /**
    * Opens the {@link JMLKeywordWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param derivedProfile The {@link IEditableDerivedProfile} which will contain the keyword.
    * @param keyword The optional existing {@link IUserDefinedKeyword} to edit.
    * @return The created {@link IUserDefinedKeyword} or {@code null} if the wizard was cancelled.
    */
   public static IUserDefinedKeyword openWizard(Shell parentShell, 
                                                IEditableDerivedProfile derivedProfile, 
                                                IUserDefinedKeyword keyword) {
      JMLKeywordWizard wizard = new JMLKeywordWizard(derivedProfile, keyword);
      WizardDialog dialog = new CustomWizardDialog(parentShell, wizard, IDialogConstants.OK_LABEL, true);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getResult();
      }
      else {
         return null;
      }
   }
}
