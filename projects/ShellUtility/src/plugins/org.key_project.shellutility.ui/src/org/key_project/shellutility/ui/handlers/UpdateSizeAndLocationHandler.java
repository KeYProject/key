package org.key_project.shellutility.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.shellutility.ui.wizard.UpdateSizeAndLocationWizard;

/**
 * Opens a {@link Wizard} which allows to define location and size of the current {@link Shell}.
 * @author Martin Hentschel
 */
public class UpdateSizeAndLocationHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);
		UpdateSizeAndLocationWizard.openWizard(window.getShell());
		return null;
	}
}
