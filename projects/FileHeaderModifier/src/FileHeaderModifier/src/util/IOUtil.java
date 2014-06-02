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

package util;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;

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
    * Reads the complete content from the {@link File}.
    * @param file The {@link File} to read from.
    * @return The read content or {@code null} if the {@link File} is {@code null}.
    * @throws IOException Occurred Exception.
    */
   public static String readFrom(File file) throws IOException {
      return file != null ? readFrom(new FileInputStream(file)) : null;
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
    * Writes the given content into the given {@link File}.
    * Nothing will be written if the content is {@code null}.
    * @param file The {@link File} to write to.
    * @param content The content to write.
    * @throws IOException Occurred Exception.
    */
   public static void writeTo(File file, String content) throws IOException {
      if (file != null) {
         writeTo(new FileOutputStream(file), content);
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
}