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

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.POBrowser;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.EnvInput;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.SLEnvInput;


//the only class in the plugin which knows KeY; 
//provides services to other plugin classes
/**
 * The main plugin class to be used in the desktop.
 * 
 * The PlugIn instance is a singleton in Eclipse, thereby use getDefault() for
 * access
 */
public class KeYPlugin extends AbstractUIPlugin 
				implements IResourceChangeListener {
    
    private static KeYPlugin instance;
    
    private IProject lastLoadedProject;
    private InitConfig lastInitConfig;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
       
    /**
     * Should only be called by Eclipse environment. 
     * Elsewhere, use getInstance().
     */
    public KeYPlugin() {
	assertTrue(instance == null);
	instance = this;
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Returns the parameter types of the passed method in KeY representation.
     */
    private ListOfKeYJavaType getParameterKJTs(IMethod method, 
	    				       JavaInfo javaInfo) {
	ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST;
	
	IType declaringType         = method.getDeclaringType();
	String[] parameterTypeNames = method.getParameterTypes();
	for(int i = 0; i < parameterTypeNames.length; i++) {
	    String javaTypeName 
	    	= EclipseSignaturesHelper.determineJavaType(
	    						parameterTypeNames[i], 
	    						declaringType);

	    if(javaTypeName == null) {
		showErrorMessage("Error determining signature types", 
				 "Could not resolve type " 
			          + parameterTypeNames[i]
			          + "! This is probably a syntax problem, "
			          + " check your import statements.");
		return null;	
	    }
	    
	    KeYJavaType kjt = javaInfo.getKeYJavaTypeByClassName(javaTypeName);
	    result = result.append(kjt);
	}
	
	return result;
    }
    
    
    /**
     * Returns the passed method in KeY representation.
     */
    private ProgramMethod getProgramMethod(IMethod method, JavaInfo javaInfo) {
	try {
	    //determine container type
	    IType containerType = method.getDeclaringType();
	    String containerTypeName = containerType.getFullyQualifiedName();
	    KeYJavaType containerKJT 
	    	= javaInfo.getTypeByClassName(containerTypeName);

	    //determine parameter types
	    ListOfKeYJavaType signature = getParameterKJTs(method, javaInfo);

	    //determine name ("<init>" for constructors)
	    String methodName = method.isConstructor()
	    			? "<init>"
	    			: method.getElementName();

	    //ask javaInfo
	    ProgramMethod result 
	    	= javaInfo.getProgramMethod(containerKJT,
	    				    methodName,
	    				    signature,
	    				    containerKJT);
	    if(result == null) {
		showErrorMessage("Error looking up method",
			"ProgramMethod not found: \"" 
			+ methodName
			+ "\nsignature: " + signature
			+ "\ncontainer: " + containerType);
	    }

	    return result;
	} catch(JavaModelException e) {
	    showErrorMessage("JavaModelException", e.getMessage());
	    return null;
	}
    }
    
	
    /**
     * Loads the passed project into the KeY prover.      
     * Is synchronized to protect loadedProjects against simultaneous
     * manipulation by the resource change listeners.
     * 
     * TODO: recursively parse source fragments linked from anywhere else -
     * sensefully integrateable in KeY ??
     */
    private synchronized InitConfig loadProject(IProject project) 
    		throws ProofInputException {
	assertTrue(project != null);
	if(project.equals(lastLoadedProject)) {
	    assertTrue(lastInitConfig != null);
	    return lastInitConfig;
	}

	//get java path, create EnvInput
	File location = project.getLocation().toFile();
	EnvInput envInput = new SLEnvInput(location.getAbsolutePath());
	
	//call ProblemInitializer
	ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	InitConfig result = pi.prepare(envInput);
	lastLoadedProject = project;
	lastInitConfig    = result;
	return result;
    }
    
    
    /**
     * Used since assertion failures / thrown Exceptions seem to be silently 
     * ignored by Eclipse at some level...
     */
    private static void assertTrue(boolean b) {
	if(!b) {
	    System.out.println("Assertion failed");
	    (new RuntimeException()).printStackTrace(System.out);
	    assert false;
	}
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Returns the shared instance.
     */
    public static KeYPlugin getInstance() {
	assertTrue(instance != null);
	return instance;
    }
    
    
    /**
     * This method is called upon plug-in activation
     */
    public void start(BundleContext context) throws Exception {			
	super.start(context);
	assertTrue(instance == this);
	Main.setStandalone(false);
	ResourcesPlugin.getWorkspace().addResourceChangeListener(
		    this, IResourceChangeEvent.POST_CHANGE);
    }

    
    /**
     * This method is called when the plug-in is stopped
     */
    public void stop(BundleContext context) throws Exception {
	super.stop(context);
	assertTrue(instance == this);
	instance = null;
	ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
    }
    
    
    public synchronized void resourceChanged(IResourceChangeEvent event) {
	//If resources in the last loaded project are changed, clear
	//cache for corresponding initConfig
	IResourceDelta delta = (event == null ? null : event.getDelta());
	IResource resource = (delta == null ? null : delta.getResource());
	IProject project = (resource == null ? null : resource.getProject());
	if(project == null || project.equals(lastLoadedProject)) {
	    lastLoadedProject = null;
	    lastInitConfig    = null;
	}
    }
    
    
    public void showErrorMessage(String title, String message) {
	MessageDialog.openError(PlatformUI.getWorkbench()
					  .getActiveWorkbenchWindow()
					  .getShell(),
		                title, 
				message);
    }

    
    /**
     * starts the KeY Prover in standalone mode (i.e. no Project 
     * selection required)	
     */
    public void openKeY() {
	Main.setStandalone(false);
	Main.getInstance(true).toFront();
    }
    
    
    /** 
     * Lets the user choose a PO for the selected project and starts
     * an according proof.
     */
    public void startProof(IProject project, IMethod method) {
	openKeY();
	
	//load project
	InitConfig initConfig = null;
	try {
	    initConfig = loadProject(project);
	} catch(ProofInputException e) {
	    showErrorMessage("Proof Input Exception",
		              "The following problem occurred when "
		              + "loading the project \"" 
		              + project.getName() + "\" into the KeY prover:\n" 
		              + e.getMessage());
	    return;
	}
	
	//determine method for which a proof should be started
	ProgramMethod pm = method == null 
	                   ? null : getProgramMethod(method, 
				    initConfig.getServices().getJavaInfo());
	
	//show PO browser
	POBrowser poBrowser = POBrowser.showInstance(initConfig, pm);
	if(poBrowser.getPO() == null) {
	    return;
	}
	
	//start proof
	ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	try {
	    pi.startProver(initConfig, poBrowser.getPO());
	} catch(ProofInputException e)  {
	    MessageDialog.openError(PlatformUI.getWorkbench()
		    .getActiveWorkbenchWindow().getShell(),
		    "Proof Input Exception",
		    "The following problem occurred when starting the proof:\n"
		    + e.getMessage());
	    return;
	}	
    }
    
    
    public void startProof(IProject project) {
	startProof(project, null);
    }
}
