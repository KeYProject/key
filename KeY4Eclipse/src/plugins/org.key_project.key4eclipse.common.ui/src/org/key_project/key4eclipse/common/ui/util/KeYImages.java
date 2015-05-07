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

package org.key_project.key4eclipse.common.ui.util;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.common.ui.Activator;
import org.key_project.util.eclipse.BundleUtil;

/**
 * <p>
 * Provides the images of the Symbolic Execution Debugger based on KeY.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP)))}
 * </p>
 * @author Martin Hentschel
 */
public final class KeYImages {
    /**
     * The key for the image that is used for method calls.
     */
    public static final String KEY_LOGO = "org.key_project.key4eclipse.common.ui.keyLogo";

    /**
     * The key for the image that is used for test generation.
     */
    public static final String TEST_GENERATION = "org.key_project.key4eclipse.common.ui.testGeneration";

    /**
     * The key for the image that is used for the starter wizard.
     */
    public static final String STARTER_WIZARD = "org.key_project.key4eclipse.common.ui.starterWizard";

    /**
     * The key for the image that is used for the interactive rule application wizard.
     */
    public static final String INTERACTIVE_WIZARD = "org.key_project.key4eclipse.common.ui.interactiveWizard";

    /**
     * The key for the image that is used for the new KeY Java project wizard.
     */
    public static final String NEW_KEY_JAVA_PROJECT_WIZARD = "org.key_project.key4eclipse.common.ui.newKeYJavaProjectWizard";

    /**
     * The key for suspend at breakpoints icon.
     */
    public static final String STOP_AT_BREAKPOINTS = "org.key_project.key4eclipse.common.ui.suspendAtbreakpoints";

    /**
     * The key for a key file wizard.
     */
    public static final String KEY_FILE_WIZARD = "org.key_project.key4eclipse.common.ui.keyFileWizard";

    /**
     * The key for a key file export wizard.
     */
    public static final String KEY_FILE_EXPORT_WIZARD = "org.key_project.key4eclipse.common.ui.keyFileExportWizard";
    
    /**
     * Forbid instances.
     */
    private KeYImages() {
    }
    
    /**
     * Returns the {@link Image} for the given key. The images are shared
     * with other plug-ins. The caller is <b>not</b> responsible for the destruction.
     * For this reason it is forbidden to call {@link Image#dispose()} on
     * a used {@link Image}.
     * @param key The key that identifies the needed {@link Image}. Use one of the constants provided by this class.
     * @return The {@link Image} or {@code null} if it was not possible to get it.
     */
    public static Image getImage(String key) {
        ImageRegistry imageRegistry = Activator.getDefault().getImageRegistry();
        Image image = imageRegistry.get(key);
        if (image == null) {
            synchronized (imageRegistry) { // Make sure that the image is created only once
               image = imageRegistry.get(key); // Make sure that the image is still not available
               if (image == null) { 
                  image = createImage(key);
                  if (image != null) {
                     imageRegistry.put(key, image);
                  }
               }
            }
        }
        return image;
    }
    
    /**
     * Returns the {@link ImageDescriptor} for the given key.
     * @param key The key.
     * @return The {@link ImageDescriptor} or {@code null} if not available.
     */
    public static ImageDescriptor getImageDescriptor(String key) {
       ImageRegistry imageRegistry = Activator.getDefault().getImageRegistry();
       ImageDescriptor descriptor = imageRegistry.getDescriptor(key);
       if (descriptor == null) {
          synchronized (imageRegistry) { // Make sure that the image is created only once
             descriptor = imageRegistry.getDescriptor(key); // Make sure that the image is still not available
             if (descriptor == null) {
                Image image = createImage(key);
                imageRegistry.put(key, image);
                descriptor = imageRegistry.getDescriptor(key);
             }
          } 
       }
       return descriptor;
    }
    
    /**
     * Returns the {@link URL} to the given key.
     * @param key The key.
     * @return The {@link URL} to the given key.
     */
    public static URL getURL(String key) {
       String path = getPath(key);
       return Activator.getDefault().getBundle().getEntry(path);
    }

    /**
     * Creates an {@link Image} for the given key.
     * @param key The key that identifies the image. Use one of the constants provided by this class.
     * @return The created {@link Image} or {@code null} if it was not possible.
     */
    protected static Image createImage(String key) {
        // Compute path to image in bundle.
        String path = getPath(key);
        // Load image if possible
        if (path != null) {
           InputStream in = null;
           try {
              in = BundleUtil.openInputStream(Activator.PLUGIN_ID, path);
              return new Image(Display.getDefault(), in);
           }
           catch (IOException e) {
              LogUtil.getLogger().logError(e);
              return null;
           }
           finally {
              try {
                 if (in != null) {
                    in.close();
                }
             }
             catch (IOException e) {
                LogUtil.getLogger().logError(e);
             }
           }
        }
        else {
           return null;
        }
    }
    
    /**
     * Returns the path to the given key.
     * @param key The key.
     * @return The path.
     */
    protected static String getPath(String key) {
       String path = null;
       if (KEY_LOGO.equals(key)) {
          path = "icons/logo16.gif";
       }
       else if (TEST_GENERATION.equals(key)) {
          path = "icons/testGeneration.png";
       }
       else if (STARTER_WIZARD.equals(key)) {
          path = "icons/start_wizard.png";
       }
       else if (INTERACTIVE_WIZARD.equals(key)) {
          path = "icons/interactive_wizard.png";
       }
       else if (NEW_KEY_JAVA_PROJECT_WIZARD.equals(key)) {
          path = "icons/new_key_java_wizard.png";
       }
       else if (STOP_AT_BREAKPOINTS.equals(key)) {
          path = "icons/stopAtBreakpoints.gif";
       }
       else if (KEY_FILE_WIZARD.equals(key)) {
          path = "icons/key_file_wizard.png";
       }
       else if (KEY_FILE_EXPORT_WIZARD.equals(key)) {
          path = "icons/key_file_export_wizard.png";
       }
       return path;
    }
}