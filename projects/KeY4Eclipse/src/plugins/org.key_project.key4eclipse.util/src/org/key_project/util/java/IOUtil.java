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

package org.key_project.util.java;

import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.LinkedList;
import java.util.List;

import javax.swing.Icon;
import javax.swing.filechooser.FileSystemView;

import org.eclipse.core.runtime.Assert;
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
    * Computes the MD5 checksum of the given {@link File}.
    * @param file The {@link File} to compute its MD5 checksum.
    * @return The computed MD5 checksum.
    * @throws IOException Occurred Exception.
    */
   public static String computeMD5(File file) throws IOException {
      if (file == null) {
         throw new IOException("Can't compute MD5 without a File.");
      }
      if (!file.isFile()) {
         throw new IOException("Can't compute MD5, because \"" + file + "\" is not an existing file.");
      }
      return computeMD5(new FileInputStream(file));
   }

   /**
    * Computes the MD5 checksum of the given {@link InputStream} and closes it.
    * @param in The {@link InputStream} which provides the content to compute its MD5 checksum. The {@link InputStream} will be closed.
    * @return The computed MD5 checksum.
    * @throws IOException Occurred Exception.
    */
   public static String computeMD5(InputStream in) throws IOException {
      if (in == null) {
         throw new IOException("Can't compute MD5 without an InputStream.");
      }
      try {
         MessageDigest digest = MessageDigest.getInstance("MD5");
         byte[] buffer = new byte[8192];
         int read = 0;
         while( (read = in.read(buffer)) > 0) {
            digest.update(buffer, 0, read);
         }
         byte[] md5sum = digest.digest();
         BigInteger bigInt = new BigInteger(1, md5sum);
         return bigInt.toString(16);
      }
      catch (NoSuchAlgorithmException e) {
         throw new IOException("Algorithm MD5 is not available.");
      }
      finally {
         in.close();
      }
   }
   
   /**
    * Returns the home directory.
    * @return The home directory.
    */
   public static File getHomeDirectory() {
      String path = System.getProperty("user.home");
      if (path != null) {
         return new File(path);
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the file extension of the given {@link File} if available.
    * @param file The file to extract it extension.
    * @return The file extension or {@code null} if not available.
    */
   public static String getFileExtension(File file) {
      if (file != null) {
         String name = file.getName();
         if (name != null) {
            int dotIndex = name.lastIndexOf(".");
            if (dotIndex >= 0) {
               return name.substring(dotIndex + 1);
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
    * Returns the file name without file extension for the given file name with extension.
    * @param file The file name with extension for that the file name without extension is needed.
    * @return The file name without extension or {@code null} if it was not possible to compute it.
    */
   public static String getFileNameWithoutExtension(String fileName) {
      if (fileName != null) {
         int dotIndex = fileName.lastIndexOf('.');
         if (dotIndex >= 0) {
            return fileName.substring(0, dotIndex);
         }
         else {
            return fileName;
         }
      }
      else {
         return null;
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
    * Reads the complete content from the {@link File}.
    * @param file The {@link File} to read from.
    * @return The read content or {@code null} if the {@link File} is {@code null} or not an existing file.
    * @throws IOException Occurred Exception.
    */
   public static String readFrom(File file) throws IOException {
      if (file != null && file.isFile()) {
         return readFrom(new FileInputStream(file));
      }
      else {
         return null;
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
    * Computes line information for each text line in the given {@link File}.
    * A {@link LineInformation} consists of the offset from the beginning of the
    * file for each line and the indices of tabs {@code '\t'} in each line.
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
    * result[0] = new LineInformation(0, new int[0]);
    * result[1] = new LineInformation(7, new int[] {7});
    * result[2] = new LineInformation(30, new int[0]);
    * result[3] = new LineInformation(31, new int[0]);
    * </code></pre>
    * </p>
    * @param file The given {@link File}.
    * @return The computed start indices.
    * @throws IOException Occurred Exception.
    */
   public static LineInformation[] computeLineInformation(File file) throws IOException {
      if (file != null) {
         return computeLineInformation(new FileInputStream(file));
      }
      else {
         return computeLineInformation((InputStream)null);
      }
   }

   /**
    * <p>
    * Computes line information for each text line in the given {@link InputStream}.
    * A {@link LineInformation} consists of the offset from the beginning of the
    * file for each line and the indices of tabs {@code '\t'} in each line.
    * </p>
    * <p>
    * Example content, line break is '\n':
    * <pre>
    * Line 1
    * Line 2:\tWith some text
    * 
    * Line 4
    * </pre>
    * Computed line start indices:
    * <pre><code>
    * result[0] = new LineInformation(0, new int[0]);
    * result[1] = new LineInformation(7, new int[] {7});
    * result[2] = new LineInformation(30, new int[0]);
    * result[3] = new LineInformation(31, new int[0]);
    * </code></pre>
    * </p>
    * @param file The given {@link File}.
    * @return The computed start indices.
    * @throws IOException Occurred Exception.
    */
   public static LineInformation[] computeLineInformation(InputStream in) throws IOException {
      InputStreamReader reader = null;
      try {
         List<LineInformation> result = new LinkedList<LineInformation>();
         if (in != null) {
            reader = new InputStreamReader(in);
            char[] buffer = new char[BUFFER_SIZE]; // Buffer with the read signs
            int read; // The number of read signs
            int startIndex = 0; // The accumulated start index over all read buffers
            int lastSignWasRBreakIndex = -1; // If this is a positive index it indicates that the last buffer ends with '\r' which must now be handled. The absolute result index is stored in this variable
            int lastIndex = 0; // The index to add to the result when the next line break sing '\r' or '\n' is read
            List<Integer> tabIndices = new LinkedList<Integer>();
            // Iterate over the whole content of the given stream
            while ((read = reader.read(buffer)) >= 1) {
               for (int i = 0; i < read; i++) {
                  if ('\n' == buffer[i]) {
                     // Check for possible line breaks with "\r\n"
                     if (lastSignWasRBreakIndex >= 0) {
                        // Handle line break with "\r\n"
                        result.add(new LineInformation(lastSignWasRBreakIndex, tabIndices));
                        lastSignWasRBreakIndex = -1;
                        tabIndices.clear();
                     }
                     else {
                        // Handle normal line breaks with '\n'
                        result.add(new LineInformation(lastIndex, tabIndices));
                        tabIndices.clear();
                     }
                     lastIndex = startIndex + i + 1;
                  }
                  else if ('\r' == buffer[i]) {
                     // Handle double line break with "\r\r" normally if required
                     if (lastSignWasRBreakIndex >= 0) {
                        result.add(new LineInformation(lastSignWasRBreakIndex, tabIndices));
                        lastSignWasRBreakIndex = -1;
                        tabIndices.clear();
                     }
                     // Check for possible line breaks with "\r\n"
                     if (i < buffer.length - 1) {
                        if ('\n' != buffer[i + 1]) {
                           // Handle normal line breaks with '\r'
                           result.add(new LineInformation(lastIndex, tabIndices));
                           lastIndex = startIndex + i + 1;
                           tabIndices.clear();
                        }
                     }
                     else {
                        // Can't check for line break with "\r\n", do check after reading next content
                        lastSignWasRBreakIndex = lastIndex;
                        lastIndex = startIndex + i + 1;
                     }
                  }
                  else if ('\t' == buffer[i]) {
                     tabIndices.add(Integer.valueOf(i - lastIndex));
                  }
               }
               startIndex += read;
            }
            // Handle last read '\r' sign if no more content was read
            if (lastSignWasRBreakIndex >= 0) {
               result.add(new LineInformation(lastSignWasRBreakIndex, tabIndices));
               tabIndices.clear();
            }
            // Handle last read '\r' or '\n' sign if no more content was read
            if (lastIndex >= 0) {
               result.add(new LineInformation(lastIndex, tabIndices));
               tabIndices.clear();
            }
         }
         return result.toArray(new LineInformation[result.size()]);
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
    * A line information returned from {@link IOUtil#computeLineInformation(File)} and
    * {@link IOUtil#computeLineInformation(InputStream)}.
    * @author Martin Hentschel
    */
   public static class LineInformation {
      /**
       * The offset of the line from beginning of the file.
       */
      private int offset;
      
      /**
       * The indices of all tabs in the line.
       */
      private int[] tabIndices;
      
      /**
       * Constructor.
       * @param offset The offset of the line from beginning of the file.
       * @param tabIndices The indices of all tabs in the line.
       */
      public LineInformation(int offset, List<Integer> tabIndices) {
         this.offset = offset;
         if (tabIndices != null) {
            this.tabIndices = new int[tabIndices.size()];
            int i = 0;
            for (Integer index : tabIndices) {
               Assert.isNotNull(index);
               this.tabIndices[i] = index.intValue();
               i++;
            }
         }
         else {
            this.tabIndices = new int[0];
         }
      }

      /**
       * Returns the indices of all tabs in the line.
       * @return The indices of all tabs in the line.
       */
      public int getOffset() {
         return offset;
      }

      /**
       * Returns the indices of all tabs in the line.
       * @return The indices of all tabs in the line.
       */
      public int[] getTabIndices() {
         return tabIndices;
      }
      
      /**
       * <p>
       * Computes for the given column index (a tab represents multiple columns) 
       * in this line information the normalized column index in that each tab character
       * represents only one sign.
       * </p>
       * <p>
       * Example line: {@code AB\tCD EF GH\t\tIJ\t.}<br>
       * Example normalizations:
       * <pre>
       * normalizeColumn(0, 3) = 0 which is character 'A'
       * normalizeColumn(1, 3) = 1 which is character 'B'
       * normalizeColumn(2, 3) = 2 which is character '  '
       * normalizeColumn(3, 3) = 2 which is character '  '
       * normalizeColumn(4, 3) = 2 which is character '  '
       * normalizeColumn(5, 3) = 3 which is character 'C'
       * normalizeColumn(6, 3) = 4 which is character 'D'
       * normalizeColumn(7, 3) = 5 which is character ' '
       * normalizeColumn(8, 3) = 6 which is character 'E'
       * normalizeColumn(9, 3) = 7 which is character 'F'
       * normalizeColumn(10, 3) = 8 which is character ' '
       * normalizeColumn(11, 3) = 9 which is character 'G'
       * normalizeColumn(12, 3) = 10 which is character 'H'
       * normalizeColumn(13, 3) = 11 which is character '   '
       * normalizeColumn(14, 3) = 11 which is character '   '
       * normalizeColumn(15, 3) = 11 which is character '   '
       * normalizeColumn(16, 3) = 12 which is character '   '
       * normalizeColumn(17, 3) = 12 which is character '   '
       * normalizeColumn(18, 3) = 12 which is character '   '
       * normalizeColumn(19, 3) = 13 which is character 'I'
       * normalizeColumn(20, 3) = 14 which is character 'J'
       * normalizeColumn(21, 3) = 15 which is character '   '
       * normalizeColumn(22, 3) = 15 which is character '   '
       * normalizeColumn(23, 3) = 15 which is character '   '
       * normalizeColumn(24, 3) = 16 which is character '.'
       * normalizeColumn(25, 3) = 17
       * normalizeColumn(26, 3) = 18
       * </pre>
       * </p>
       * @param column The column where tabs represents multiple characters. If the column is negative this value is returned. 
       * @param tabWidth The tab width which must be greater as {@code 1}, otherwise the column index is returned.
       * @return The normalized column where tabs represents only one character.
       */
      public int normalizeColumn(int column, int tabWidth) {
         if (column >= 0 && tabWidth >= 2) {
            int result = column;
            boolean goOn = true;
            int i = 0;
            while (goOn) {
               goOn = i < tabIndices.length && tabIndices[i] < column - (i * (tabWidth - 1));
               if (goOn) {
                  result -= (tabWidth - 1);
                  i++;
               }
            }
            if (i - 1 >= 0 && i - 1 < tabIndices.length) {
               if (column - (i - 1) * (tabWidth - 1) >= tabIndices[i - 1] && column - (i - 1) * (tabWidth - 1) < tabIndices[i - 1] + tabWidth - 1) {
                  result += column - (i - 1) * (tabWidth - 1) - tabIndices[i - 1];
               }
            }
            return result;
         }
         else {
            return column;
         }
      }
   }

   /**
    * Creates a temporary directory with help of {@link File#createTempFile(String, String)}.
    * @param prefix The prefix string to be used in generating the file's name; must be at least three characters long.
    * @param suffix The suffix string to be used in generating the file's name; may be null, in which case the suffix ".tmp" will be used.
    * @return Created temporary directory.
    * @throws IOException Occurred Exception.
    */
   public static File createTempDirectory(String prefix, String suffix) throws IOException {
      File tempFile = File.createTempFile(prefix, suffix);
      if (!tempFile.delete()) {
         throw new IOException("Can't delete temp file, reason is unknown.");
      }
      if (!tempFile.mkdir()) {
         throw new IOException("Can't create temp directory, reason is unknown.");
      }
      return tempFile;
   }
   
   /**
    * Searches recursive in the given {@link File} all {@link File}s accepted
    * by the given {@link IFilter}.
    * @param file The {@link File} to start search in.
    * @param filter An optional {@link IFilter} used to accept files. Without a filter all {@link File}s are accepted.
    * @return The accepted {@link File}s.
    * @throws IOException Occurred Exception
    */
   public static List<File> search(File file, final IFilter<File> filter) throws IOException {
      final List<File> result = new LinkedList<File>();
      if (file != null) {
         visit(file, new IFileVisitor() {
            @Override
            public void visit(File visitedFile) {
               if (filter == null || filter.select(visitedFile)) {
                  result.add(visitedFile);
               }
            }
         });
      }
      return result;
   }
   
   /**
    * Visits recursive all files and folders.
    * @param file The {@link File} to start in.
    * @param visitor The {@link IFileVisitor} which does something with the visited files
    * @throws IOException Occurred Exception
    */
   public static void visit(File file, IFileVisitor visitor) throws IOException {
      if (file != null && visitor != null) {
         visitor.visit(file);
         File[] children = file.listFiles();
         if (children != null) {
            for (File child : children) {
               visit(child, visitor);
            }
         }
      }
   }
   
   /**
    * A visitor which does something with {@link File}s.
    * @author Martin Hentschel
    */
   public static interface IFileVisitor {
      /**
       * Do something with the visited {@link File}.
       * @param file The visited {@link File}.
       * @throws IOException Occurred Exception
       */
      public void visit(File file) throws IOException;
   }
   
   /**
    * Replaces all line breaks ({@code \r}, {@code \r\n}) in the given InputStream with {@code \n}.
    * @param in The {@link InputStream} to replace line breaks in.
    * @return A new {@link InputStream} with with the replaced line breaks.
    * @throws IOException Occurred Exception.
    */
   public static InputStream unifyLineBreaks(InputStream in) throws IOException {
      if (in != null) {
         String text = IOUtil.readFrom(in);
         text = text.replace("\r\n", "\n");
         text = text.replace("\r", "\n");
         return new ByteArrayInputStream(text.getBytes());
      }
      else {
         return null;
      }
   }
}