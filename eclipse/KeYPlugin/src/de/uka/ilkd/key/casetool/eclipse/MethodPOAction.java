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

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.gui.JMLPOAndSpecProvider;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.jml.JMLSpec;
import de.uka.ilkd.key.proof.init.AssignableCheckProofOblInput;

/**
 * @author Marius Hillenbrand
 *
 * Action which lets the user select proof obligations for a method.
 * This action is selectable from the context menu of a java method.
 */
public class MethodPOAction implements IObjectActionDelegate {

    ISelection selection;
    
	// quick-and-dirty for syncExec(dialog.open()) in swt thread
	MethodPOSelectionDialog dialog;
	int                    state;
	
	/**
	 * Constructor for Action1.
	 */
	public MethodPOAction() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}


	/**
	 * @see IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
//		MessageDialog.openInformation(
//			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(),
//			"KeYPlugIn Plug-in",
//			"KeY Action was executed.");

		//new MethodPOSelectionDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), new Vector()).open();
		
		
		if(selection != null && selection instanceof StructuredSelection) {
		    IMethod selectedMethod = (IMethod) 
		    		((StructuredSelection)selection).getFirstElement();
		    ICompilationUnit srcFile = selectedMethod.getCompilationUnit();
		    
		    if(srcFile==null) {
		        MessageDialog.openError(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(),
		                "Not source method", "The method you selected does not exist in source form. " +
		                "It cannot be used for a proof.");
		    } else {
		        // TODO generalize to consider packageFragmentRoots (needed to support
		        // special source locations like folders only linked into the eclipse
		        // project
		        IProject project = srcFile.getJavaProject().getProject();
		        
		        // assure the sources are parsed
		        int status = KeYPlugin.getDefault().assertProjectParsed(project, false);
				// int status = KeYPlugin.PROJECT_ALREADY_OPEN;
				
				if(status==KeYPlugin.PROJECT_ALREADY_OPEN ||
						status == KeYPlugin.PROJECT_LOAD_SUCESSFUL) {
					// determine the encapsulating class of the selected method
			        IType declaringType = selectedMethod.getDeclaringType();
			        
			        // extract signature of method
			        //int paramCount = selectedMethod.getNumberOfParameters();
			        try {
	                    //selectedMethod.get
	                    String[] parameterNames = selectedMethod.getParameterNames();
	                    String[] parameterTypes = selectedMethod.getParameterTypes(); 
	                    ListOfString sigStrings = SLListOfString.EMPTY_LIST;
	                
	                    for(int i = 0; i<parameterNames.length; i++) {
	                        // System.out.println(parameterNames[i]+" \"" +parameterTypes[i]+"\"");
	                        
							String javaType = 
								EclipseSignaturesHelper.determineJavaType(parameterTypes[i], declaringType);
							
							if(javaType!=null) {
								sigStrings = sigStrings.append(javaType);
							} else {
								MessageDialog.openError(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(),
										"Error determining signature types !", "Could not resolve type "
										+parameterTypes[i]+" of the method's parameter "+parameterNames[i]+" !"
										+" This is probably a syntax problem, check your import statements.");
								return;	
							}
	                    }
	                        
	    		        
	    		        JMLPOAndSpecProvider provider = 
	    		            Main.getInstance().getJMLPOAndSpecProvider();
						Main.getInstance().toBack();
                        
						Vector methodSpecs = provider.getMethodSpecs(declaringType.getFullyQualifiedName(), 
								selectedMethod.getElementName(), sigStrings);
						dialog = new MethodPOSelectionDialog(
								PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), methodSpecs);
						state = dialog.open();
						
						boolean allInvariants = dialog.isAllInvariantsSelected();
						boolean addInvariantsToPostCondition = 
                            dialog.isAddInvariantsToPostConditionSelected();
						
						if(state == Window.OK) {
							Object selectedPO = dialog.getSelectionOnOK().getFirstElement();
							//System.out.println("Selected proof obligation: "+selectedPO);
							
							// TODO complete this step-by-step
							// assignable: see JML Specification browser
							//boolean assignablePO = (selectedPO instanceof AssignableCheckProofOblInput);
							if(selectedPO instanceof AssignableCheckProofOblInput) {
								AssignableCheckProofOblInput assignableCheckPO = (AssignableCheckProofOblInput) selectedPO;
								provider.createPOandStartProver(assignableCheckPO.getSpec(), allInvariants, addInvariantsToPostCondition, true);
								//assignableCheckPO.get
								
							} else if(selectedPO instanceof JMLSpec){
								provider.createPOandStartProver((JMLSpec) selectedPO, allInvariants, addInvariantsToPostCondition, false);
								
							} else {
								// TODO handle error case
							}
						}
						
	                } catch (JavaModelException e) {
	                    // TODO Auto-generated catch block
	                    e.printStackTrace();
	                }
				}
		    }
		}
	}

	
    /**
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	    this.selection = selection;
	}

}
