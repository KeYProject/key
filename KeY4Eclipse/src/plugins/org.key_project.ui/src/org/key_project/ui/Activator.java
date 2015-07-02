package org.key_project.ui;

import java.io.File;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.key_project.ui.util.EclipseKeYDesktop;
import org.key_project.ui.util.KeYExampleUtil;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.osgi.framework.BundleContext;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ExitMainAction;
import de.uka.ilkd.key.settings.PathConfig;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "org.key_project.ui"; //$NON-NLS-1$

	// The shared instance
	private static Activator plugin;
	
	/**
	 * The constructor
	 */
	public Activator() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		// Deactivate experimental features
		Main.setEnabledExperimentalFeatures(false);
	   // Make sure that the system is not exited when the KeY main window is closed.
      Main.setKeyDesktop(new EclipseKeYDesktop());
	   ExitMainAction.exitSystem = false;
	   Main.showExampleChooserIfExamplesDirIsDefined = false;
	   // Change the KeY config path to store configuration files inside the workspace.
	   String keyConfigDir = getDefault().getStateLocation().toString();
	   PathConfig.setKeyConfigDir(keyConfigDir + File.separator + PathConfig.KEY_DIRECTORY_NAME);
	   // Check if a local example directory is available. This is true if the plug-in is used inside a development IDE
	   String exampleDir = KeYExampleUtil.getLocalExampleDirectory();
	   if (exampleDir == null || !new File(exampleDir).isDirectory()) {
         // Extract KeY examples into workspace, this is required to use them.
         exampleDir = keyConfigDir + File.separator + "examples";
         String keyExampleFile = keyConfigDir + File.separator + "examples.properties";
         String actualVersion = getBundle().getVersion().toString();
         KeYExampleUtil.updateExampleDirectory(actualVersion, 
                                               PLUGIN_ID, 
                                               ExampleChooser.EXAMPLES_PATH.replace(File.separatorChar, '/'), 
                                               keyExampleFile, 
                                               exampleDir);
	   }
	   Main.setExamplesDir(exampleDir);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	   // Close main window of KeY to store settings
	   if (MainWindow.hasInstance()) {
         final MainWindow main = MainWindow.getInstance();
         if (main.getExitMainAction() != null) {             
             IRunnableWithResult<Boolean> runnable = new AbstractRunnableWithResult<Boolean>() {
                @Override
                public void run() {
                    // Closing the window causes a deadlock under OS X;
                    // hence we just save the settings here (because eclipse will call System.exit later)
                    main.getExitMainAction().saveSettings();                    
                    setResult(Boolean.TRUE);
                }
            };
            SwingUtil.invokeLater(runnable);
            while (runnable.getResult()==null) {
                Thread.sleep(10);
            }
         }            
	   }
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return plugin;
	}

}
