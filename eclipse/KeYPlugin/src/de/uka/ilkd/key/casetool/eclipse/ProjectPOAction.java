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

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;



/**
 * Action which opens KeY, loads the current project, and opens the PO browser.
 * This action is selectable in the context menu of a class (in the outline)
 * or a java file (in the Package Explorer)
 */
public class ProjectPOAction extends Action 
	implements IObjectActionDelegate, IWorkbenchWindowActionDelegate {
    
    ISelection selection = null;
    
    
    public ProjectPOAction() {
        setEnabled(false);    	
    }
    

    private IJavaProject getSelectedJavaProject() {
        if(selection != null && selection instanceof StructuredSelection) {            
            final StructuredSelection structuredSelection 
            	= (StructuredSelection)selection;       
            Object tmpSelected = structuredSelection.getFirstElement();
            if (tmpSelected instanceof IJavaProject) {
                return (IJavaProject)tmpSelected;
            }    	            
            
        }
        return null;
    }


    public void setActivePart(IAction action, IWorkbenchPart targetPart) {
    }
    
    
    public void run(IAction action) {
	try {
	    IJavaProject javaProject = getSelectedJavaProject();
	    if(javaProject != null) {
		KeYPlugin.getInstance().startProof(javaProject.getProject());
	    }
	} catch(Throwable e) {
	    KeYPlugin.getInstance().showErrorMessage(e.getClass().getName(), 
		    				     e.getMessage());
	    e.printStackTrace(System.out);
	}	
    }
    
    
    public void selectionChanged(IAction action, ISelection selection) {
        this.selection = selection;
        final boolean actionEnabled = getSelectedJavaProject() != null;        
        action.setEnabled(actionEnabled);
        this.setEnabled(actionEnabled);
    }
    
    
    public void dispose() {
    }
    
    
    public void init(IWorkbenchWindow window) { 
    }
}
