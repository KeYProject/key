package de.uka.ilkd.key.casetool.eclipse;
/*
 * This file is part of KeY - Integrated Deductive Software Design
 * Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
 *                        Universitaet Koblenz-Landau, Germany
 *                        Chalmers University of Technology, Sweden
 *
 * The KeY system is protected by the GNU General Public License.
 */

import java.util.Vector;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;


/**
 * @author Marius Hillenbrand
 * NOT USED by KeYPlugin any more, but by VisualDebugger (TODO: Move there).
 */
public class MethodPOSelectionDialog extends Dialog {

	ListViewer          viewer;
	IStructuredSelection	selectionOnOK;
	Button				allInvariantsButton;
	Button				addInvariantsToPostConditionButton;
	boolean				allInvariants;
	boolean				addInvariantsToPostCondition;
	Vector              methodPOInput;
	
	private final class MethodPOSelectionLabelProvider extends LabelProvider {
	    
        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ILabelProvider#getText(java.lang.Object)
         */
        public String getText(Object element) {
            
            // quick-and-dirty beautification of the selection dialog
            
            String fullProofDescription = element.toString();
            
            StringBuffer out = new StringBuffer(fullProofDescription);
            
            int recentLineLength = 0;
            
            boolean eraseRemainingLine = false;
            
            for(int pos=0; pos<out.length();) {
                char c = out.charAt(pos);
                
                if(eraseRemainingLine) {
                    
                    if(c!='\n') {
                        out.deleteCharAt(pos);
                        
                    } else {
                        out.insert(pos,"...");
                        eraseRemainingLine = false;
                        recentLineLength = 0;
                        pos+=4;
                    }
                    
                } else {
                   
                   if(c=='\n') {
                       recentLineLength = 0;
                       pos++;
                       
                   } else {
                       recentLineLength++;
                       pos++;
                       
                       if(recentLineLength>=70)
                           eraseRemainingLine = true;
                   }  
                }
            }
            return out.toString();
        }
}

    /**
	 * A StructuredContentProvider is used in the eclipse jface viewer framework to feed
	 * model data into a viewer.
	 * In this case we provide the list of selectable proof obligations for a list viewer
	 */
	private class MethodPOContentProvider implements IStructuredContentProvider {
		
		ListViewer viewer;
		
		public MethodPOContentProvider() {
			super();
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.IContentProvider#dispose()
		 */
		public void dispose() {
			// nothing to do here
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
		 * Does nothing, since we do not need to store/process the input element ourself.
		 */
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
			
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
		 * Here we extract the possible proof obligations from the input vector.
		 * This method will be called by the ListViewer after the input vector has been fed
		 * via setInput() 
		 */
		public Object[] getElements(Object inputElement) {
			
			if(inputElement instanceof Vector) {
				Vector v = (Vector) inputElement;
				Object entries [] = new Object[v.size()];
				
				for(int i=0; i<v.size(); i++) {
					entries[i] = v.get(i);
				}
				
				return entries;
				
			} else {
				return null;
			}
		}
	}
	
	
	/**
	 * @param parentShell
	 * @param methodPOInput the vector of possible proof obligations the user shall choose from
	 */
	public MethodPOSelectionDialog(Shell parentShell, Vector methodPOInput) {
		super(parentShell);
		this.methodPOInput = methodPOInput;
	}
	
	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.Dialog#okPressed()
	 */
	protected void okPressed() {
		// preserve for evaluation after the dialog has been closed and the viewer
		// widget is possibly disposed
		selectionOnOK = (IStructuredSelection) viewer.getSelection();
		
		allInvariants               = allInvariantsButton.getSelection();
		addInvariantsToPostCondition = addInvariantsToPostConditionButton.getSelection();
		
		// if no PO has been selected, display an error
		// otherwise close dialog (normal way of operation)
		if(selectionOnOK.size() == 0 ) {
			MessageDialog.openError(getShell(), "No proof obligation selected",
					"Select one of the provided proof obligations first.");
		} else {
			super.okPressed();
		}
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.window.Window#configureShell(org.eclipse.swt.widgets.Shell)
	 */
	protected void configureShell(Shell newShell) {
		// that much effort for a simple window title
		super.configureShell(newShell);
		newShell.setText("Select desired proof obligation for this method");
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.Dialog#createDialogArea(org.eclipse.swt.widgets.Composite)
	 */
	protected Control createDialogArea(Composite parent) {
		
		Composite composite = (Composite) super.createDialogArea(parent);
		
		
		Label label = new Label(composite, SWT.NONE);
		label.setText("JML specifications for selected method:");
		
		List list = new List(composite, SWT.BORDER | SWT.SINGLE | SWT.H_SCROLL);
		viewer = new ListViewer(list);
		
		//new ListViewer()
		
		// use our own content provider
		viewer.setContentProvider(new MethodPOContentProvider());
		// use predefined label provider which uses toString() as text and null as image
		viewer.setLabelProvider(new MethodPOSelectionLabelProvider());
		
		viewer.setInput(methodPOInput);
		
		allInvariantsButton = new Button(composite, SWT.CHECK);
		allInvariantsButton.setText("Use all applicable invariants");
		allInvariantsButton.setSelection(true);
		addInvariantsToPostConditionButton = new Button(composite, SWT.CHECK);
		addInvariantsToPostConditionButton.setText("Add invariants to postcondition");
		
		composite.layout();
		
		return composite;
	}
	
	/**
	 * @return Returns the selectionOnOK.
	 */
	public IStructuredSelection getSelectionOnOK() {
		return selectionOnOK;
	}


	/**
	 * @return Returns the addInvariantsToPostCondition.
	 */
	public boolean isAddInvariantsToPostConditionSelected() {
		return addInvariantsToPostCondition;
	}
	
	/**
	 * @return Returns the allInvariants.
	 */
	public boolean isAllInvariantsSelected() {
		return allInvariants;
	}
	
}
