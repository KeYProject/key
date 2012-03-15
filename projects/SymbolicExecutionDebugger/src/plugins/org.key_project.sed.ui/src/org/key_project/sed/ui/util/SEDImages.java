package org.key_project.sed.ui.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.ui.Activator;
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
public final class SEDImages {
    /**
     * The key for the image that is used for method calls.
     */
    public static final String METHOD_CALL = "org.key_project.sed.ui.images.methodCall";
    
    /**
     * The key for the image that is used for method return.
     */
    public static final String METHOD_RETURN = "org.key_project.sed.ui.images.methodReturn";
    
    /**
     * The key for the image that is used for termination.
     */
    public static final String TERMINATION = "org.key_project.sed.ui.images.termination";
    
    /**
     * The key for the image that is used for branch node.
     */
    public static final String BRANCH_NODE = "org.key_project.sed.ui.images.branchNode";
    
    /**
     * The key for the image that is used for branch condition.
     */
    public static final String BRANCH_CONDITION = "org.key_project.sed.ui.images.branchCondition";
    
    /**
     * The key for the image that is used for exceptional termination.
     */
    public static final String EXCEPTIONAL_TERMINATION = "org.key_project.sed.ui.images.exceptionalTermination";
    
    /**
     * Forbid instances.
     */
    private SEDImages() {
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
        Image image = Activator.getDefault().getImageRegistry().get(key);
        if (image == null) {
            image = createImage(key);
            if (image != null) {
                Activator.getDefault().getImageRegistry().put(key, image);
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
        if (METHOD_CALL.equals(key)) {
           path = "icons/method_call.gif";
        }
        else if (METHOD_RETURN.equals(key)) {
           path = "icons/method_return.gif";
        }
        else if (TERMINATION.equals(key)) {
           path = "icons/termination.gif";
        }
        else if (BRANCH_NODE.equals(key)) {
           path = "icons/branch_node.gif";
        }
        else if (BRANCH_CONDITION.equals(key)) {
           path = "icons/branch_condition.gif";
        }
        else if (EXCEPTIONAL_TERMINATION.equals(key)) {
           path = "icons/exceptional_termination.gif";
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
               registry.remove(METHOD_CALL);
               registry.remove(METHOD_RETURN);
               registry.remove(TERMINATION);
               registry.remove(BRANCH_NODE);
               registry.remove(BRANCH_CONDITION);
               registry.remove(EXCEPTIONAL_TERMINATION);
            }
         });
       }
    }
}
