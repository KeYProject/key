package org.key_project.javaeditor.outline;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.javaeditor.util.LogUtil;
import org.key_project.util.eclipse.BundleUtil;

public final class OutlineJMLPicture {

   public static final String JML_LOGO = "org.key_project.jmlediting.ui.jmlLogo";

   /**
    * Private Constructor - no instances allowed.
    */
   private OutlineJMLPicture() {
   }

   /**
    * Method to get the {@link Image} that should be used in the outline as Picture to
    * represent an JML Element.
    * 
    * @return The Image used for JML
    */
   public static Image getimage() {

      // load image from disk.
      InputStream in = null;
      try {
         in = BundleUtil.openInputStream("org.key_project.jmlediting.ui",
                  "icons/jml-writing-16x16.png");
      }
      catch (IOException e) {
         LogUtil.getLogger().logError(e);
      }

      return new Image(Display.getDefault(), in);

   }
}
