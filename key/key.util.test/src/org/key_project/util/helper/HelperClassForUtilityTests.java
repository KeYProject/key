package org.key_project.util.helper;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import junit.framework.TestCase;

import org.key_project.util.java.IOUtil;

public class HelperClassForUtilityTests {
   public static final String RESOURCE_DIRECTORY;
   
   static {
      File projectRoot = IOUtil.getProjectRoot(HelperClassForUtilityTests.class);
      // Update path in Eclipse Plug-ins executed as JUnit Test.
      if ("org.key_project.util.test".equals(projectRoot.getName())) {
         projectRoot = projectRoot.getParentFile().getParentFile().getParentFile().getParentFile();
         projectRoot = new File(projectRoot, "key" + File.separator + "key.util.test");
      }
      // Update path in Eclipse Plug-ins executed as JUnit Plug-in Test.
      else if ("tests".equals(projectRoot.getName())) {
         projectRoot = projectRoot.getParentFile().getParentFile().getParentFile();
         projectRoot = new File(projectRoot, "key" + File.separator + "key.util.test");
      }
      RESOURCE_DIRECTORY = projectRoot + File.separator + "resources";
   }

   /**
    * Creates a folder.
    * @param folder The folder to create.
    * @return The created folder.
    */
   public static File createFolder(File folder) {
       TestCase.assertEquals(!folder.exists(), folder.mkdirs());
       TestCase.assertTrue(folder.exists());
       TestCase.assertTrue(folder.isDirectory());
       return folder;
   }
   
   /**
    * Creates a file
    * @param file The file to create.
    * @param content The content to write to file.
    * @return The created file.
    * @throws IOException Occurred Exception.
    */
   public static File createFile(File file, String content) throws IOException {
       FileWriter writer = null;
       try {
           writer = new FileWriter(file);
           writer.write(content);
           TestCase.assertTrue(file.exists());
           TestCase.assertTrue(file.isFile());
           return file;
       }
       finally {
           if (writer != null) {
               writer.close();
           }
       }
   }
}
