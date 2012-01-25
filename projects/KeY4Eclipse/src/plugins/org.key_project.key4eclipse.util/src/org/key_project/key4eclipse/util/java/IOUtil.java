/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.java;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

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
}