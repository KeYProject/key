/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse;

import java.io.File;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.key_project.key4eclipse.event.RefreshProofSaverListener;
import org.key_project.key4eclipse.util.KeYExampleUtil;
import org.osgi.framework.BundleContext;

import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ExitMainAction;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

    // The plug-in ID
    public static final String PLUGIN_ID = "org.key_project.key4eclipse"; //$NON-NLS-1$

    // The shared instance
    private static Activator plugin;
    
    /**
     * The used {@link RefreshProofSaverListener}.
     */
    private static final RefreshProofSaverListener refreshListener = new RefreshProofSaverListener();

    /**
     * The constructor
     */
    public Activator() {
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext
     * )
     */
    public void start(BundleContext context) throws Exception {
        super.start(context);
        plugin = this;
        // Make sure that the system is not exited when the KeY main window is closed.
        ExitMainAction.exitSystem = false;
        Main.showExampleChooserIfExamplesDirIsDefined = false;
        // Change the KeY config path to store configuration files inside the workspace.
        String keyConfigDir = getDefault().getStateLocation().toString();
        PathConfig.setKeyConfigDir(keyConfigDir + File.separator + PathConfig.KEY_DIRECTORY_NAME);
        // Check if a local example directory is available. This is true if the plug-in is used inside a development IDE
        String exampleDir = KeYExampleUtil.getLocalExampleDirectory();
        if (exampleDir == null || exampleDir.isEmpty()) {
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
        // Make sure that when a proof is saved the workspace resources are updated
        ProofSaver.addProofSaverListener(refreshListener);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
     * )
     */
    public void stop(BundleContext context) throws Exception {
       ProofSaver.removeProofSaverListener(refreshListener);
        plugin = null;
        super.stop(context);
        // Close main window of KeY to store settings
        if (MainWindow.hasInstance()) {
            MainWindow main = MainWindow.getInstance();
            if (main.getExitMainAction() != null) {
                main.getExitMainAction().exitMainWithoutInteraction();
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

    /**
     * Returns an image descriptor for the image file at the given plug-in
     * relative path
     * 
     * @param path
     *            the path
     * @return the image descriptor
     */
    public static ImageDescriptor getImageDescriptor(String path) {
        return imageDescriptorFromPlugin(PLUGIN_ID, path);
    }
}