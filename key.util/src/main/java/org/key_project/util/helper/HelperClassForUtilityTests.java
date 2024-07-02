package org.key_project.util.helper;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

public class HelperClassForUtilityTests {
    public static final File RESOURCE_DIRECTORY = FindResources.getTestResourcesDirectory();

   /**
    * Creates a folder.
    * @param folder The folder to create.
    * @return The created folder.
    */
   public static File createFolder(File folder) {
       if(!folder.exists()) folder.mkdirs();
       /*TestCase.assertEquals(!folder.exists(), folder.mkdirs());
       TestCase.assertTrue(folder.exists());
       TestCase.assertTrue(folder.isDirectory());*/
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
       try(FileWriter writer = new FileWriter(file)) {
           writer.write(content);
           //TestCase.assertTrue(file.exists());
           //TestCase.assertTrue(file.isFile());
           return file;
       }
   }
}
