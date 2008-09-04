//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.eclipse;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;


/**
 * Action which opens KeY, loads the current project, and opens the PO browser
 * for a specific method.
 * This action is selectable from the context menu of a java method.
 */
public class MethodPOAction implements IObjectActionDelegate {
    
    private ISelection selection;
    

    public void setActivePart(IAction action, IWorkbenchPart targetPart) {
    }


    public void run(IAction action) {
	if(selection == null || !(selection instanceof StructuredSelection)) {
	    return;
	}
	
	try {
	    //determine selected method and project
	    IMethod method 
	    = (IMethod) ((StructuredSelection)selection).getFirstElement();
	    ICompilationUnit srcFile = method.getCompilationUnit();
	    if(srcFile == null) {
		KeYPlugin.getInstance().showErrorMessage(
			"Not source method", 
			"The method you selected does not "
			+ "exist in source form. It cannot "
			+ "be used for a proof.");
		return;
	    }	
	    IProject project = srcFile.getJavaProject().getProject();

	    //start proof
	    KeYPlugin.getInstance().startProof(project, method);
	} catch(Throwable e) {
	    KeYPlugin.getInstance().showErrorMessage(e.getClass().getName(), 
		    				     e.getMessage());
	    e.printStackTrace(System.out);
	}
    }


    public void selectionChanged(IAction action, ISelection selection) {
	this.selection = selection;
    }
}
