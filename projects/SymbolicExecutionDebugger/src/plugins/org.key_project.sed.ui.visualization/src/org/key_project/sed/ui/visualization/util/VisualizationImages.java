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

package org.key_project.sed.ui.visualization.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.ui.visualization.Activator;
import org.key_project.util.eclipse.BundleUtil;

/**
 * <p>
 * Provides the visualization images of the Symbolic Execution Debugger based on KeY.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code VisualizationImages.getImage(VisualizationImages.SET_FILE)))}
 * </p>
 * @author Martin Hentschel
 */
public final class VisualizationImages {
    /**
     * The key for the image that is used for SET Files.
     */
    public static final String SET_FILE = "org.key_project.sed.ui.visualization.images.SETFile";
    
    /**
     * Forbid instances.
     */
    private VisualizationImages() {
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
     * Creates an {@link Image} for the given key.
     * @param key The key that identifies the image. Use one of the constants provided by this class.
     * @return The created {@link Image} or {@code null} if it was not possible.
     */
    protected static Image createImage(String key) {
       // Compute path to image in bundle.
       String path = null;
       if (SET_FILE.equals(key)) {
           path = "icons/symbolic_debug.gif";
       }
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
     * Disposes all contained images. This method is automatically called
     * when the plug-in is unloaded from the {@link Activator}.
     * There is no need to call it from any other place!
     */
    public static void disposeImages() {
       Display display = Display.getDefault();
       if (!display.isDisposed()) {
          display.syncExec(new Runnable() {
            @Override
            public void run() {
               ImageRegistry registry = Activator.getDefault().getImageRegistry();
               registry.remove(SET_FILE);
            }
         });
       }
    }
}