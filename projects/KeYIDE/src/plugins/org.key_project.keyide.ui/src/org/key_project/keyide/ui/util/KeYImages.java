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

package org.key_project.keyide.ui.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.keyide.ui.Activator;
import org.key_project.keyide.ui.util.LogUtil;
import org.key_project.util.eclipse.BundleUtil;

/**
 * <p>
 * Provides the images of the Symbolic Execution Debugger based on KeY.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP)))}
 * </p>
 * @author Martin Hentschel, Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public final class KeYImages {
   // TODO: Document constants of KeYImages
   public static final String FOLDER = "org.key_project.keyide.ui.images.folder";
   public static final String FOLDER_PROVED = "org.key_project.keyide.ui.images.folderProved";
   public static final String NODE = "org.key_project.keyide.ui.images.node";
   public static final String NODE_PROVED = "org.key_project.keyide.ui.images.nodeProved";

   /**
    * Forbid instances.
    */
   private KeYImages(){
   }

   /**
    * Returns the {@link Image} for the given key. The caller is <b>not</b> responsible for the destruction.
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
       if (FOLDER.equals(key)) {
          path = "icons/folder.png";
       }
       else if (FOLDER_PROVED.equals(key)) {
          path = "icons/folderproved.png";
       }
       else if (NODE.equals(key)) {
          path = "icons/ekey-mono16.gif";
       }
       else if (NODE_PROVED.equals(key)) {
          path = "icons/keyproved16.gif";
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
              registry.remove(FOLDER);
              registry.remove(FOLDER_PROVED);
              registry.remove(NODE);
              registry.remove(NODE_PROVED);
           }
        });
      }
   }
}