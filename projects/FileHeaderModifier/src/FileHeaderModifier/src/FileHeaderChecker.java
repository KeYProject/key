import java.io.File;
import java.io.FileFilter;
import java.util.LinkedList;
import java.util.List;

import util.IOUtil;

/**
 * This program lists the files which have not the given header.
 * @author Martin Hentschel
 */
public class FileHeaderChecker {
   /**
    * The program entry point.
    * @param args The program start parameters.
    */
   public static void main(String[] args) {
      try {
         // Define settings
         File workingDir = new File("D:\\Forschung\\GIT\\KeY_Master\\projects");
         File newHeaderFile = new File("data/NewHeader.txt");
         FileFilter filter = new FileFilter() {
            @Override
            public boolean accept(File file) {
               if (file.isFile()) {
                  String extension = IOUtil.getFileExtension(file);
                  return extension != null && "java".equals(extension.toLowerCase());
               }
               else {
                  return true;
               }
            }
         };
         // Write settings into console
         System.out.println("Working Directory: " + workingDir);
         System.out.println("New Header File: " + newHeaderFile);
         System.out.println();
         // List files to check
         List<File> filesToModify = new LinkedList<File>();
         FileHeaderModifier.listFiles(workingDir, filter, filesToModify);
         // Read headers
         String newHeader = IOUtil.readFrom(newHeaderFile).trim();
         // Modify files and write result to output directory
         for (File oldFile : filesToModify) {
            // Check if content starts with header
            String content = IOUtil.readFrom(oldFile).trim();
            if (!content.startsWith(newHeader)) {
               System.out.println("Missing Header: " + oldFile);
            }
         }
      }
      catch (Exception e) {
         e.printStackTrace();
      }
   }
}
