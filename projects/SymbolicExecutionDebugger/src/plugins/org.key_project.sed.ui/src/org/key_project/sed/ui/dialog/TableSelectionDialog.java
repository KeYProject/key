package org.key_project.sed.ui.dialog;

import org.eclipse.jface.dialogs.TrayDialog;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.widgets.Shell;

public class TableSelectionDialog extends TrayDialog {

    public TableSelectionDialog(IShellProvider parentShell) {
        super(parentShell);
    }

    public TableSelectionDialog(Shell shell) {
        super(shell);
    }
}
