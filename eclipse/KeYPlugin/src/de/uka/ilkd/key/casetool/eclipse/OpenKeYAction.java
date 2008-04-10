//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                  Universitaet Koblenz-Landau, Germany
//                  Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.eclipse;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

/**
 * Action which opens KeY without loading anything into it.
 */
public class OpenKeYAction extends Action 
				implements IWorkbenchWindowActionDelegate {
	
    public void dispose() {		
    }

    public void init(IWorkbenchWindow window) {
    }

    public void run(IAction action) {
	try {
	    KeYPlugin.getInstance().openKeY();
	} catch(Throwable e) {
	    KeYPlugin.getInstance().showErrorMessage(e.getClass().getName(), 
		    				     e.getMessage());
	    e.printStackTrace(System.out);
	}
    }

    public void selectionChanged(IAction action, ISelection selection) {
    }
}
