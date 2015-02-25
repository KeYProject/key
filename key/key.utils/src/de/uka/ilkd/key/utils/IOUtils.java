package de.uka.ilkd.key.utils;

import java.io.File;
import java.net.URI;
import java.net.URL;
import java.security.CodeSource;

public final class IOUtils {
   private IOUtils() {
   }

   public static final File getClassLocation(Class<?> classInstance) {
      if (classInstance != null) {
         CodeSource cs = classInstance.getProtectionDomain().getCodeSource();
         return cs != null ? toFile(cs.getLocation()) : null;
      }
      else {
         return null;
      }
   }

   public static final File getProjectRoot(Class<?> classInstance) {
      File file = getClassLocation(classInstance);
      return file != null ? file.getParentFile() : null;
   }

   public static File toFile(URL url) {
      return new File(toURI(url));
   }
   
   public static String toFileString(URL url) {
      File file = toFile(url);
      return file != null ? file.getAbsolutePath() : null;
   }
   
   public static URI toURI(URL url) {
      return url != null ? URI.create(url.toString()) : null;
   }
}
