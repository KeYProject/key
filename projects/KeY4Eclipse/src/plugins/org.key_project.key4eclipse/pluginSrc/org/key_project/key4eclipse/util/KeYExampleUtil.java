/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.key4eclipse.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.net.URLConnection;
import java.util.Enumeration;
import java.util.Properties;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.key_project.key4eclipse.Activator;
import org.osgi.framework.Bundle;

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
       String exampleDir = KeYExampleUtil.getLocalExampleDirectory();
       return new File(exampleDir, "02-Subset" + File.separator + "project.key");
    }

    /**
     * Returns a specified example directory in bundle file "customTargets.xml".
     * This file is only available if the plug-in was loaded in a started
     * Eclipse product via the Eclipse development IDE. In a real deployed
     * product it will return {@code null}.
     * @return The local example directory or {@code null} if it is not available.
     */
    public static String getLocalExampleDirectory() {
        String localKeyHome = getLocalKeYHomeDirectory();
        return localKeyHome != null ? localKeyHome + File.separator + ExampleChooser.EXAMPLES_PATH : null;
    }

    /**
     * Returns a specified KeY external library directory in bundle file "customTargets.xml".
     * This file is only available if the plug-in was loaded in a started
     * Eclipse product via the Eclipse development IDE. In a real deployed
     * product it will return {@code null}.
     * @return The local library directory or {@code null} if it is not available.
     */
    public static String getLocalKeYExtraLibsDirectory() {
        return getLocalPropertyValue("ext.dir");
    }

    /**
     * Returns a specified KeY repository home directory in bundle file "customTargets.xml".
     * This file is only available if the plug-in was loaded in a started
     * Eclipse product via the Eclipse development IDE. In a real deployed
     * product it will return {@code null}.
     * @return The local KeY repository directory or {@code null} if it is not available.
     */
    public static String getLocalKeYHomeDirectory() {
        return getLocalPropertyValue("key.rep");
    }

    /**
     * Returns a specified value in bundle file "customTargets.xml".
     * This file is only available if the plug-in was loaded in a started
     * Eclipse product via the Eclipse development IDE. In a real deployed
     * product it will return {@code null}.
     * @param key The key for that the value should be returned if possible.
     * @return The value or {@code null} if it is not available.
     */
    public static String getLocalPropertyValue(String key) {
        if (key != null) {
            Properties props = getLocalProperties();
            if (props != null) {
                String dir = props.getProperty(key);
                if (dir != null && dir.trim().length() >= 1) {
                    return dir.trim();
                }
                else {
                    return null;
                }
            }
            else {
                return null;
            }
        }
        else {
            return null;
        }
    }

    /**
     * Returns the properties in bundle file "customTargets.xml".
     * This file is only available if the plug-in was loaded in a started
     * Eclipse product via the Eclipse development IDE. In a real deployed
     * product it will return {@code null}.
     * @return The properties or {@code null} if it is not available.
     */
    public static Properties getLocalProperties() {
        try {
            if (Activator.getDefault() != null) {
                Bundle bundle = Activator.getDefault().getBundle();
                URL customTargetsURL = bundle.getEntry("customTargets.properties");
                if (customTargetsURL != null) {
                    InputStream in = null;
                    try {
                        in = customTargetsURL.openStream();
                        Properties props = new Properties();
                        props.load(in);
                        return props;
                    }
                    finally {
                        if (in != null) {
                            in.close();
                        }
                    }
                }
                else {
                    return null;
                }
            }
            else {
                return null; // Plug-in is not loaded, may used in normal Java application
            }
        }
        catch (IOException e) {
            return null; // Nothing to do.
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
                delete(dir);
                dir.mkdirs();
                extractFromBundleToFilesystem(bundleId, pathInBundle, dir);
            }
        }
    }
    
    /**
     * Deletes the given file/folder with all contained sub files/folders.
     * @param file The file/folder to delete.
     */
    public static void delete(File file) {
        if (file != null && file.exists()) {
            if (file.isDirectory()) {
                File[] children = file.listFiles();
                for (File child : children) {
                    delete(child);
                }
            }
            file.delete();
        }
    }

    /**
     * Extracts the specified files from the bundle into the target directory.
     * @param pluginId The ID of the plug-in that contains the data to extract.
     * @param pathInBundle The path in the bundle to extract.
     * @param target The target directory in the local file system.
     * @throws CoreException Occurred Exception.
     */
    public static void extractFromBundleToFilesystem(String pluginId, String pathInBundle, File target) throws CoreException {
        // Make sure that all parameters are defined.
        if (pluginId == null) {
            throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No plug-in ID defined."));
        }
        if (pathInBundle == null) {
            throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No path in plug-in defined."));
        }
        if (target == null) {
            throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No target is defined."));
        }
        // Get Bundle.
        Bundle bundle = Platform.getBundle(pluginId);
        if (bundle == null) {
            throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Can't find plug-in with ID \"" + pluginId + "\"."));
        }
        // Search entries.
        Enumeration<?> entries = bundle.findEntries(pathInBundle, "*", true);
        if (entries != null) {
            // Make sure that target exists
            target.mkdirs();
            // Extract entries
            while (entries.hasMoreElements()) {
                Object entry = entries.nextElement();
                if (entry instanceof URL) {
                    URL url = (URL) entry;
                    String urlPath = url.getPath();
                    int pathInBundleIndex = urlPath.indexOf(pathInBundle);
                    String pathInTarget = urlPath.substring(pathInBundleIndex + pathInBundle.length());
                    InputStream in = null;
                    try {
                        FileOutputStream out = null;
                        try {
                            // Check if it is a file or folder by the content size.
                            URLConnection connection = url.openConnection();
                            if (connection.getContentLength() > 0) {
                                in = connection.getInputStream();
                                File file = new File(target, pathInTarget);
                                out = new FileOutputStream(file);
                                int read;
                                byte[] buffer = new byte[1024 * 10];
                                while ((read = in.read(buffer)) >= 0) {
                                    out.write(buffer, 0, read);
                                }
                            }
                            else {
                                // Handle URL as folder (Happens in product execution)
                                File folder = new File(target, pathInTarget);
                                if (!folder.exists()) {
                                    folder.mkdirs();
                                }
                            }
                        }
                        finally {
                            if (out != null) {
                                out.close();
                            }
                        }
                    }
                    catch (IOException e) {
                        // Handle URL as folder (This happens in IDE execution)
                        File folder = new File(target, pathInTarget);
                        if (!folder.exists()) {
                            folder.mkdirs();
                        }
                    }
                    finally {
                        try {
                            if (in != null) {
                                in.close();
                            }
                        }
                        catch (IOException e) {
                            // Nothing to do.
                        }
                    }
                }
                else {
                    throw new IllegalArgumentException("Unsupported bundle entry \"" + entry + "\".");
                }
            }
        }
    }
}