package de.uka.ilkd.key.casetool.eclipse;
/*
 * This file is part of KeY - Integrated Deductive Software Design
 * Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
 *                         Universitaet Koblenz-Landau, Germany
 *                         Chalmers University of Technology, Sweden
 *
 * The KeY system is protected by the GNU General Public License.
 */

import org.eclipse.core.resources.IProject;
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
 * @author Marius Hillenbrand
 * 
 * Action which opens the JML Specification browser on a project.
 * This action is selectable in the context menu of a class (in the outline)
 * or a java file (in the Package Explorer)
 */
public class JavaProjectJMLBrowserAction extends Action implements IObjectActionDelegate, 
IWorkbenchWindowActionDelegate {
    
    ISelection selection = null;
    
    
    public JavaProjectJMLBrowserAction() {
        setEnabled(false);    	
    }
    
    /* (non-Javadoc)
     * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(org.eclipse.jface.action.IAction, org.eclipse.ui.IWorkbenchPart)
     */
    public void setActivePart(IAction action, IWorkbenchPart targetPart) {
    }
    
    /* (non-Javadoc)
     * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
     */
    public void run(IAction action) {
        IJavaProject javaProject = getSelectedJavaProject();
        if (javaProject != null) {
            IProject project = javaProject.getProject();
            
            int result = KeYPlugin.getDefault().assertProjectParsed(project, true);
            
            if(result == KeYPlugin.PROJECT_ALREADY_OPEN)
                KeYPlugin.getDefault().openJMLSpecBrowserOnCurrentLoadedModel();
            // otherwise an error occured, the operation was aborted,
            // or the JML Specification browser is opened when loading the
            // java model
        }    
    }
    
    private void enable(IAction action) {
        final boolean actionEnabled = getSelectedJavaProject() != null;
        action.setEnabled(actionEnabled);
        this.setEnabled(actionEnabled);
    }
    
    /* (non-Javadoc)
     * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
     */
    public void selectionChanged(IAction action, ISelection selection) {
        this.selection = selection;      
        enable(action);
    }
    
    private IJavaProject getSelectedJavaProject() {
        if(selection != null && selection instanceof StructuredSelection) {            
            final StructuredSelection structuredSelection = (StructuredSelection)selection;       
            Object tmpSelected = structuredSelection.getFirstElement();
            if (tmpSelected instanceof IJavaProject) {
                return (IJavaProject)tmpSelected;
            }    	            
            
        }
        return null;
    }
    
    public void dispose() {
    }
    
    public void init(IWorkbenchWindow window) { }
    
}
