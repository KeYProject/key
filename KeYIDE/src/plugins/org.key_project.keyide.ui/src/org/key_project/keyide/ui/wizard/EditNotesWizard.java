package org.key_project.keyide.ui.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.keyide.ui.wizard.page.EditNotesWizardPage;

import de.uka.ilkd.key.proof.Node;

/**
 * {@link Wizard} to edit notes of a {@link Node}.
 * @author Martin Hentschel
 */
public class EditNotesWizard extends Wizard {
   /**
    * The {@link Node} to edit.
    */
   private final Node node;
   
   /**
    * Constructor.
    * @param node The {@link Node} to edit.
    */
   public EditNotesWizard(Node node) {
      this.node = node;
      setWindowTitle("Edit Notes");
      setHelpAvailable(false);
   }

   /**
    * The used {@link EditNotesWizardPage}.
    */
   private EditNotesWizardPage editPage;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      editPage = new EditNotesWizardPage("editPage", node.getNodeInfo().getNotes());
      addPage(editPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      node.getNodeInfo().setNotes(editPage.getNotes());
      return true;
   }
   
   /**
    * Opens the {@link EditNotesWizard}.
    * @param parentShell The parent {@link Shell}.
    * @param node The {@link Node} to edit.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, Node node) {
      WizardDialog dialog = new WizardDialog(parentShell, new EditNotesWizard(node));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
