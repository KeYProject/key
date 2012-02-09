package org.key_project.key4eclipse.util.java;

import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import javax.swing.Icon;
import javax.swing.filechooser.FileSystemView;

import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.util.eclipse.swt.ImageUtil;

/**
 * Provides static methods to work with java IO.
 * @author Martin Hentschel
 */
public final class IOUtil {
   /**
    * The size of used buffers.
    */
   public static final int BUFFER_SIZE = 1024 * 10;
   
   /**
    * Forbid instances by this private constructor.
    */
   private IOUtil() {
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
    * Reads the compelte content from the {@link InputStream} and closes it.
    * @param in The {@link InputStream} to read from and to close.
    * @return The read content or {@code null} if the {@link InputStream} is {@code null}.
    * @throws IOException Occurred Exception.
    */
   public static String readFrom(InputStream in) throws IOException {
      InputStreamReader reader = null;
      try {
         if (in != null) {
            reader = new InputStreamReader(in);
            StringBuffer sb = new StringBuffer();
            char[] buffer = new char[BUFFER_SIZE];
            int read;
            while ((read = reader.read(buffer)) > 1) {
               sb.append(buffer, 0, read);
            }
            return sb.toString();
         }
         else {
            return null;
         }
      }
      finally {
         if (reader != null) {
            reader.close();
         }
         if (in != null) {
            in.close();
         }
      }
   }

   /**
    * <p>
    * Returns the file system icon for the given existing file.
    * </p>
    * <p>
    * <b>Attention: </b> The caller is responsible to dispose the created {@link Image}!
    * </p>
    * @param file The file for that the system icon is needed.
    * @return The file system icon or {@code null} if no existing file is given.
    */
   public static Image getFileSystemIcon(File file) {
       Image image = null;
       if (file != null && file.exists()) {
           FileSystemView view = FileSystemView.getFileSystemView();
           if (view != null) {
               Icon icon = view.getSystemIcon(file);
               if (icon != null) {
                   BufferedImage bufferedImage = ImageUtil.toBufferedImage(icon);
                   ImageData imageData = ImageUtil.convertToImageData(bufferedImage);
                   image = new Image(Display.getDefault(), imageData);
               }
           }
       }
       return image;
   }
}