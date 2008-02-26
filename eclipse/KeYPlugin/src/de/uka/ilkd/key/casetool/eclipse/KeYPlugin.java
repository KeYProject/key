package de.uka.ilkd.key.casetool.eclipse;

/*
 * This file is part of KeY - Integrated Deductive Software Design
 * Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
 *                        Universitaet Koblenz-Landau, Germany
 *                        Chalmers University of Technology, Sweden
 *
 * The KeY system is protected by the GNU General Public License.
 */

import java.io.File;
import java.util.LinkedList;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.proof.init.EnsuresPostPO;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * @author Marius Hillenbrand
 * 
 * The main plugin class to be used in the desktop.
 * 
 * The PlugIn instance is a singleton in Eclipse, thereby use getDefault() for
 * access
 */
/**
 * @author hillen
 * 
 */
public class KeYPlugin extends AbstractUIPlugin implements
		IResourceChangeListener {

	/**
	 * Nested class to analyze resource change deltas.
	 * If resources in a project whose source code we loaded into KeY are changed,
	 * remove it from the list of loaded projects. 
	 */
	private final class ProjectChangeDeltaInspector implements IResourceDeltaVisitor {

		/* (non-Javadoc)
		 * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
		 */
		public boolean visit(IResourceDelta delta) throws CoreException {
			
			IProject containingProject = delta.getResource().getProject();
			// if a proof has been started in this project and the sourcecode has been marked as loaded
			// remove this now to trigger a reload when a new proof is to be started
			if(loadedProjects.contains(containingProject)) {
				loadedProjects.remove(containingProject);
			}
			
			if(loadedProjects.size()==0)
				return false;
			else 
				return true;

		}
	}

	protected static final int PROJECT_ALREADY_OPEN = 1;

	protected static final int PROJECT_LOAD_SUCESSFUL = 2;

	protected static final int PROJECT_LOAD_CANCELED = 3;

	protected static final int PROJECT_LOAD_FAILED = 4;

	// The shared instance.
	private static KeYPlugin plugin;

	// Resource bundle.
	private ResourceBundle resourceBundle;

	/**
	 * a list of the javaProjects which currently have a model loaded into the
	 * KeY prover
	 */
	private LinkedList loadedProjects = new LinkedList();

	/**
	 * have we registered as resource change listener yet ?
	 */
	private boolean registeredAsResourceChangeListener = false;

	/**
	 * The constructor.
	 */
	public KeYPlugin() {
		super();
		plugin = this;
	}

	/**
	 * This method is called upon plug-in activation
	 */
	public void start(BundleContext context) throws Exception {			
		super.start(context);
		Main.standalone = false;
	}

	/**
	 * This method is called when the plug-in is stopped
	 */
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
		plugin = null;
		resourceBundle = null;
	}

	/**
	 * Returns the shared instance.
	 */
	public static KeYPlugin getDefault() {
		return plugin;
	}

	/**
	 * Returns the string from the plugin's resource bundle, or 'key' if not
	 * found.
	 */
	public static String getResourceString(String key) {
	    ResourceBundle bundle = KeYPlugin.getDefault().getResourceBundle();
	    try {
	        return (bundle != null) ? bundle.getString(key) : key;
	    } catch (MissingResourceException e) {
	        return key;
	    }
	}

	/**
	 * Returns the plugin's resource bundle,
	 */
	public ResourceBundle getResourceBundle() {
	    try {
	        if (resourceBundle == null)
	            resourceBundle = ResourceBundle
	            .getBundle("de.uka.ilkd.key.casetool.eclipse.KeYPluginResources");
	    } catch (MissingResourceException x) {
	        resourceBundle = null;
	    }
	    return resourceBundle;
	}

	/**
	 * @param project
	 * @return
	 */
	protected int assertProjectParsed(IProject project) {
		return assertProjectParsed(project, false);
	}

	/**
	 * if necessary loads the current project into the KeY prover. Is
	 * synchronized to protect LinkedList loadedProjects against simultaneous
	 * manipulation by the resource change listeners
	 * 
	 * TODO: recursively parse source fragments linked from anywhere else -
	 * sensefully integrateable in KeY ??
	 * 
	 * @param project
	 *            the eclipse project which should be loaded
	 * @param jmlBrowserIntended
	 *            is it intended to open the JML browser or would this be a
	 *            side-effect?
	 * @return status whether the project was already opened before or the load
	 *         was successful / failed
	 * 
	 */
	protected synchronized int assertProjectParsed(IProject project,
			boolean jmlBrowserIntended) {

		if (!loadedProjects.contains(project)) {

			// project's java model has not been loaded into KeY yet, do this
			// now

			String inputName = "eclipse-project_"
					+ project.getName();
			File location = project.getLocation().toFile();

			Main main = Main.getInstance(false);

			EnsuresPostPO input = null;

			if (jmlBrowserIntended) {
/*
				input = new JavaInputWithJMLSpecBrowser(inputName, location,
						false, main.getProgressMonitor());
*/
			} else {
/*				input = new JavaInput(inputName, location, main
						.getProgressMonitor());
                        */
			}

                        ProblemInitializer problemInit = new ProblemInitializer(main);
                        
                        String error = "Prover init for " + location + " failed.";
                        try {
                            problemInit.startProver(input.getPO().getFirstProof().env(), input);
                            error = "";
                        } catch (ProofInputException pie) {
                            error = pie.getMessage();
                        }

			if (error.length() == 0) {

				loadedProjects.add(project);

				// now register as resource change listener, if not done before
				if (!registeredAsResourceChangeListener) {
					ResourcesPlugin.getWorkspace().addResourceChangeListener(
							this, IResourceChangeEvent.POST_CHANGE);
					registeredAsResourceChangeListener = true;
				}
				return PROJECT_LOAD_SUCESSFUL;

			} else {

				MessageDialog.openError(PlatformUI.getWorkbench()
						.getActiveWorkbenchWindow().getShell(),
						"Error loading java model into KeY prover",
						"While loading this project, the following error"
								+ " occured:\n" + error);
				return PROJECT_LOAD_FAILED;
			}

		} else {
			return PROJECT_ALREADY_OPEN;
		}
	}

	/**
	 * Just opens the JML Specification browser in the KeY prover which knows
	 * about the java models loaded before. This may only be called *after*
	 * assertProjectParsed(), otherwise the JML Spec Bowser will only show the
	 * built-in specs.
	 */
	public void openJMLSpecBrowserOnCurrentLoadedModel() {

		Main key = Main.getInstance(true);
                Main.setStandalone(false);
		key.toFront();
		//key.showSpecBrowser();

	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org.eclipse.core.resources.IResourceChangeEvent)
	 */
	public synchronized void resourceChanged(IResourceChangeEvent event) {
		
		if(! (loadedProjects.size()==0)) { // do nothing when we don't observe any projects
			try {
				event.getDelta().accept(new ProjectChangeDeltaInspector());
			} catch (CoreException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

	}

	/**
	 * starts the KeY Prover in standalone mode (i.e. no Project selection required)	
	 */
	public void openKeY() {
		Main.getInstance(true).toFront();
                Main.setStandalone(false);
	}
}
