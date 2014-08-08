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

package org.key_project.key4eclipse.resources.ui.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.ui.Activator;
import org.key_project.util.eclipse.BundleUtil;

/**
 * <p>
 * Provides the images of the KeY Resources UI.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT)))}
 * </p>
 * @author Martin Hentschel
 */
public final class ResourcesUiImages {
    /**
     * The key for the image that is used for {@link ObserverFunctionInfo}s.
     */
    public static final String OBSERVER_FUNCTION = "org.key_project.key4eclipse.resources.ui.observerFunction";

    /**
     * The key for the image that is used for a {@link ContractInfo} of a {@link ObserverFunctionInfo}.
     */
    public static final String OBSERVER_FUNCTION_CONTRACT = "org.key_project.key4eclipse.resources.ui.observerFunctionContract";

    /**
     * The key for the image that is used for a {@link ContractInfo} of a {@link MethodInfo}.
     */
    public static final String METHOD_CONTRACT = "org.key_project.key4eclipse.resources.ui.methodContract";

    /**
     * The key for the image that is used for a {@link ContractInfo} of a {@link MethodInfo} with box modality.
     */
    public static final String METHOD_CONTRACT_BOX = "org.key_project.key4eclipse.resources.ui.methodContractBox";

    /**
     * The key for the image that is used for a {@link ContractInfo} of a {@link MethodInfo} with diamond modality.
     */
    public static final String METHOD_CONTRACT_DIAMOND = "org.key_project.key4eclipse.resources.ui.methodContractDiamond";

    /**
     * Forbid instances.
     */
    private ResourcesUiImages() {
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
     * Creates an {@link Image} for the given key.
     * @param key The key that identifies the image. Use one of the constants provided by this class.
     * @return The created {@link Image} or {@code null} if it was not possible.
     */
    protected static Image createImage(String key) {
        // Compute path to image in bundle.
        String path = null;
        if (METHOD_CONTRACT.equals(key)) {
           path = "icons/DbcOperationContract.gif";
        }
        else if (METHOD_CONTRACT_BOX.equals(key)) {
           path = "icons/DbcOperationContract_Box.gif";
        }
        else if (METHOD_CONTRACT_DIAMOND.equals(key)) {
           path = "icons/DbcOperationContract_Diamond.gif";
        }
        else if (OBSERVER_FUNCTION.equals(key)) {
           path = "icons/DbcAxiom.gif";
        }
        else if (OBSERVER_FUNCTION_CONTRACT.equals(key)) {
           path = "icons/DbCAxiomContract.gif";
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
               registry.remove(METHOD_CONTRACT);
               registry.remove(METHOD_CONTRACT_BOX);
               registry.remove(METHOD_CONTRACT_DIAMOND);
               registry.remove(OBSERVER_FUNCTION);
               registry.remove(OBSERVER_FUNCTION_CONTRACT);
            }
         });
       }
    }
}