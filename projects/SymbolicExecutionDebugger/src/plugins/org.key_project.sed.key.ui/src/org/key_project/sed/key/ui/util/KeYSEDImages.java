package org.key_project.sed.key.ui.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.sed.key.ui.Activator;

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
public final class KeYSEDImages {
    /**
     * The key for the image that is used in the main tab group of the launch configuration.
     */
    public static final String LAUNCH_MAIN_TAB_GROUP = "org.key_project.sed.key.ui.images.launchMainTabGroup";
    
    /**
     * Forbid instances.
     */
    private KeYSEDImages() {
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
        if (LAUNCH_MAIN_TAB_GROUP.equals(key)) {
            InputStream in = null;
            try {
                in = BundleUtil.openInputStream(Activator.PLUGIN_ID, "icons/logo16.gif");
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
        Activator.getDefault().getImageRegistry().remove(LAUNCH_MAIN_TAB_GROUP);
    }
}
