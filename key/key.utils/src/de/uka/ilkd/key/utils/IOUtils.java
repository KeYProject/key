package de.uka.ilkd.key.utils;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.security.CodeSource;

public final class IOUtils {
   private IOUtils() {
   }

   public static final File getClassLocation(Class<?> classInstance) {
      CodeSource cs = classInstance.getProtectionDomain().getCodeSource();
      try {
         return new File(cs.getLocation().toURI());
      }
      catch (URISyntaxException e) {
         return null;
      }
   }

   public static final File getProjectRoot(Class<?> classInstance) {
      File file = getClassLocation(classInstance);
      return file != null ? file.getParentFile() : null;
   }

   public static File toFile(URL url) {
      return new File(URI.create(url.toString()));
   }
   
   public static String toFileString(URL url) {
      File file = toFile(url);
      return file != null ? file.getAbsolutePath() : null;
   }
}
