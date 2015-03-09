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

package org.key_project.ui.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.util.Properties;

import org.eclipse.core.runtime.CoreException;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ExampleChooser;

/**
 * Provides static methods to work with the KeY examples in the Eclipse
 * integration of KeY.
 * @author Martin Hentschel
 */
public class KeYExampleUtil {
    /**
     * The key used in the example properties to store the current version.
     */
    public static final String VERSION_KEY = "exampleVersion";
    
    /**
     * Forbid instances.
     */
    private KeYExampleUtil() {
    }
    
    /**
     * Returns a *.key with a fast and simple proof.
     * @return A *.key with a fast and simple proof.
     */
    public static File getExampleProof() {
       String exampleDir = Main.getExamplesDir();
       return new File(exampleDir, "firstTouch" + File.separator + "02-Subset" + File.separator + "project.key");
    }

    /**
     * Returns a specified example directory in bundle file "customTargets.xml".
     * This file is only available if the plug-in was loaded in a started
     * Eclipse product via the Eclipse development IDE. In a real deployed
     * product it will return {@code null}.
     * @return The local example directory or {@code null} if it is not available.
     */
    public static String getLocalExampleDirectory() {
        File home = IOUtil.getProjectRoot(KeYExampleUtil.class); // Should be KeY4Eclipse\src\plugins
        if (home != null) {
           home = home.getParentFile().getParentFile().getParentFile();
           return home.getAbsolutePath() +  File.separator + "key" + File.separator + "key.ui" + File.separator + ExampleChooser.EXAMPLES_PATH;
        }
        else {
           return null;
        }
    }

    /**
     * Updates the example directory in the workspace if required. The example
     * directory is extracted from bundle and stored in the plug-in data folder
     * of this bundle together with a properties file that contains the bundle
     * version that has created the folder. If the current bundle version is
     * different to the one in the properties file the existing example
     * directory is deleted and recreated.
     * @param bundleVersion The current version
     * @param bundleId The ID of the plug-in that contains the example content.
     * @param pathInBundle The path in the plug-in to the example content.
     * @param keyExampleFile The properties file to store the bundle version in.
     * @param keyExampleDir The example directory to use.
     * @throws CoreException Occurred Exception.
     */
    public static void updateExampleDirectory(String bundleVersion,
                                               String bundleId,
                                               String pathInBundle,
                                               String keyExampleFile, 
                                               String keyExampleDir) throws CoreException {
        if (keyExampleDir != null && keyExampleFile != null) {
            // Get actual example version
            Properties properties = new Properties();
            File keyFile = new File(keyExampleFile);
            try {
                if (keyFile.exists()) {
                    properties.load(new FileReader(keyFile));
                }
            }
            catch (IOException e) {
                // Nothing to do.
            }
            if (bundleVersion != null && !bundleVersion.equals(properties.get(VERSION_KEY))) {
                // Update example version
                try {
                    properties.put(VERSION_KEY, bundleVersion);
                    properties.store(new FileOutputStream(keyFile), null);
                }
                catch (IOException e) {
                    // Nothing to do.
                }
                // Update directory.
                File dir = new File(keyExampleDir);
                IOUtil.delete(dir);
                dir.mkdirs();
                BundleUtil.extractFromBundleToFilesystem(bundleId, pathInBundle, dir);
            }
        }
    }
}