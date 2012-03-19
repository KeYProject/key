package org.key_project.util.java;

import java.awt.image.BufferedImage;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import javax.swing.Icon;
import javax.swing.filechooser.FileSystemView;

import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.widgets.Display;
import org.key_project.util.eclipse.swt.ImageUtil;

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
    * Reads the complete content from the {@link InputStream} and closes it.
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
            while ((read = reader.read(buffer)) >= 1) {
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
    * Writes the given content into the given {@link OutputStream} and closes it.
    * Nothing will be written if the content is {@code null}, but the stream will be closed.
    * @param out The {@link OutputStream} to write to.
    * @param content The content to write.
    * @throws IOException Occurred Exception.
    */
   public static void writeTo(OutputStream out, String content) throws IOException {
      PrintStream printStream = null;
      try {
         if (out != null && content != null) {
            printStream = new PrintStream(out);
            printStream.print(content);
         }
      }
      finally {
         if (out != null) {
            out.close();
         }
         if (printStream != null) {
            printStream.close();
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

   /**
    * <p>
    * Computes the start indices for each line in the given {@link File}.
    * </p>
    * <p>
    * Example content, line break is '\n':
    * <pre>
    * Line 1
    * Line 2: With some text
    * 
    * Line 4
    * </pre>
    * Computed line start indices:
    * <pre><code>
    * result[0] = 0
    * result[1] = 7
    * result[2] = 30
    * result[3] = 31
    * </code></pre>
    * </p>
    * @param file The given {@link File}.
    * @return The computed start indices.
    * @throws IOException Occurred Exception.
    */
   public static Integer[] computeLineStartIndices(File file) throws IOException {
      if (file != null) {
         return computeLineStartIndices(new FileInputStream(file));
      }
      else {
         return computeLineStartIndices((InputStream)null);
      }
   }

   /**
    * <p>
    * Computes the start indices for each line in the given {@link InputStream}.
    * </p>
    * <p>
    * Example content, line break is '\n':
    * <pre>
    * Line 1
    * Line 2: With some text
    * 
    * Line 4
    * </pre>
    * Computed line start indices:
    * <pre><code>
    * result[0] = 0
    * result[1] = 7
    * result[2] = 30
    * result[3] = 31
    * </code></pre>
    * </p>
    * @param file The given {@link File}.
    * @return The computed start indices.
    * @throws IOException Occurred Exception.
    */
   public static Integer[] computeLineStartIndices(InputStream in) throws IOException {
      
      
      InputStreamReader reader = null;
      try {
         List<Integer> result = new LinkedList<Integer>();
         if (in != null) {
            reader = new InputStreamReader(in);
            char[] buffer = new char[BUFFER_SIZE]; // Buffer with the read signs
            int read; // The number of read signs
            int startIndex = 0; // The accumulated start index over all read buffers
            int lastSignWasRBreakIndex = -1; // If this is a positive index it indicates that the last buffer ends with '\r' which must now be handled. The absolute result index is stored in this variable
            int lastIndex = 0; // The index to add to the result when the next line break sing '\r' or '\n' is read
            // Iterate over the whole content of the given stream
            while ((read = reader.read(buffer)) >= 1) {
               for (int i = 0; i < read; i++) {
                  if ('\n' == buffer[i]) {
                     // Check for possible line breaks with "\r\n"
                     if (lastSignWasRBreakIndex >= 0) {
                        // Handle line break with "\r\n"
                        result.add(Integer.valueOf(lastSignWasRBreakIndex));
                        lastSignWasRBreakIndex = -1;
                     }
                     else {
                        // Handle normal line breaks with '\n'
                        result.add(Integer.valueOf(lastIndex));
                     }
                     lastIndex = startIndex + i + 1;
                  }
                  else if ('\r' == buffer[i]) {
                     // Handle double line break with "\r\r" normally if required
                     if (lastSignWasRBreakIndex >= 0) {
                        result.add(Integer.valueOf(lastSignWasRBreakIndex));
                        lastSignWasRBreakIndex = -1;
                     }
                     // Check for possible line breaks with "\r\n"
                     if (i < buffer.length - 1) {
                        if ('\n' != buffer[i + 1]) {
                        // Handle normal line breaks with '\r'
                           result.add(Integer.valueOf(lastIndex));
                           lastIndex = startIndex + i + 1;
                        }
                     }
                     else {
                        // Can't check for line break with "\r\n", do check after reading next content
                        lastSignWasRBreakIndex = lastIndex;
                        lastIndex = startIndex + i + 1;
                     }
                  }
               }
               startIndex += read;
            }
            // Handle last read '\r' sign if no more content was read
            if (lastSignWasRBreakIndex >= 0) {
               result.add(Integer.valueOf(lastSignWasRBreakIndex));
            }
            // Handle last read '\r' or '\n' sign if no more content was read
            if (lastIndex >= 0) {
               result.add(Integer.valueOf(lastIndex));
            }
         }
         return result.toArray(new Integer[result.size()]);
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
}