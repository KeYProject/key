
package de.uka.ilkd.key.experimental;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;

/**
 * Extracted methods from
 * ./projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.util/src/org/key_project/util/java/IOUtil.java
 * which are used in {@link RunAllProofsTest}. This file is for experimental
 * purpose only and should be deleted before Java version of runAllProofs is
 * merged into master branch.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class IOUtil {
    
    /**
    * The size of used buffers.
    */
   public static final int BUFFER_SIZE = 1024 * 10;
   
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
