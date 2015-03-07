package org.key_project.key4eclipse.common.ui.counterExample;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.PreferenceManager;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.internal.dialogs.FilteredPreferenceDialog;

/**
 * The {@link FilteredPreferenceDialog} used to show SMT results.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SMTPreferenceDialog extends FilteredPreferenceDialog {
   /**
    * Constructor.
    * @param parentShell The parent {@link Shell}.
    * @param manager The {@link PreferenceManager} to use.
    */
   public SMTPreferenceDialog(Shell parentShell, PreferenceManager manager) {
      super(parentShell, manager);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void configureShell(Shell newShell) {
      super.configureShell(newShell);
      newShell.setText("SMT Counterexample Search");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void createButtonsForButtonBar(Composite parent) {
      Button cancelButton = createButton(parent, IDialogConstants.CANCEL_ID, IDialogConstants.CLOSE_LABEL, false);
      getShell().setDefaultButton(cancelButton);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateButtons() {
      // Nothing to do.
   }
}
