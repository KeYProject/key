package de.uka.ilkd.key.casetool.eclipse;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

public class OpenKeYAction extends Action 
implements IWorkbenchWindowActionDelegate {
	

	public void dispose() {		
	}

	public void init(IWorkbenchWindow window) {
	}

	public void run(IAction action) {
		KeYPlugin plugin = KeYPlugin.getDefault();
		plugin.openKeY();		
	}

	public void selectionChanged(IAction action, ISelection selection) {
	}
}
