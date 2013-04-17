import java.io.File;
import java.io.FileFilter;
import java.util.LinkedList;
import java.util.List;

import util.IOUtil;
import util.StringUtil;

/**
 * This program makes sure that each specified file has the defined header.
 * @author Martin Hentschel
 */
public class FileHeaderModifier {
   /**
    * The program entry point.
    * @param args The program start parameters.
    */
   public static void main(String[] args) {
      try {
         // Define settings
         File workingDir = new File("D:\\Forschung\\GIT\\KeY_Master\\projects");
         File outputDir = new File("C:\\temp\\test_out");
         File oldHeaderFile = new File("data/OldHeader.txt");
         File newHeaderFile = new File("data/NewHeader.txt");
         FileFilter filter = new FileFilter() {
            @Override
            public boolean accept(File file) {
               if (file.isFile()) {
                  String extension = IOUtil.getFileExtension(file);
                  return extension != null && "java".equals(extension.toLowerCase());
               }
               else {
                  return !isEclipseProjectDataFolder(file);
               }
            }
            
            protected boolean isEclipseProjectDataFolder(File file) {
               if (!file.isFile()) {
                  if (isEclipseProject(file.getParentFile())) {
                     return "data".equals(file.getName());
                  }
                  else {
                     return false;
                  }
               }
               else {
                  return false;
               }
            }
            
            protected boolean isEclipseProject(File file) {
               if (!file.isFile()) {
                  File[] projectFiles = file.listFiles(new FileFilter() {
                     @Override
                     public boolean accept(File pathname) {
                        return pathname.isFile() && ".project".equals(pathname.getName());
                     }
                  });
                  return projectFiles != null && projectFiles.length == 1;
               }
               else {
                  return false;
               }
            }
         };
         // Write settings into console
         System.out.println("Working Directory: " + workingDir);
         System.out.println("Output Directory: " + outputDir);
         System.out.println("Old Header: File" + oldHeaderFile);
         System.out.println("New Header File: " + newHeaderFile);
         System.out.println();
         // Test settings
         if (workingDir.equals(outputDir)) {
            throw new IllegalArgumentException("Working and Output Directory are the same.");
         }
         // List files to modify
         List<File> filesToModify = new LinkedList<File>();
         listFiles(workingDir, filter, filesToModify);
         // Read headers
         String oldHeader = IOUtil.readFrom(oldHeaderFile).trim();
         String newHeader = IOUtil.readFrom(newHeaderFile).trim();
         // Modify files and write result to output directory
         for (File oldFile : filesToModify) {
            // Write current file into console
            System.out.println("Modifying: " + oldFile);
            // Compute new content
            String content = IOUtil.readFrom(oldFile);
            String newContent = computeNewContent(content, oldHeader, newHeader);
            // Compute file in output dir
            int prefixLength = workingDir.toString().length();
            String path = oldFile.toString().substring(prefixLength); 
            File newFile = new File(outputDir, path);
            // Make sure that outputDir exists
            if (!newFile.getParentFile().exists()) {
               newFile.getParentFile().mkdirs();
            }
            // Create file in outputDir (Existing files will be overwritten)
            IOUtil.writeTo(newFile, newContent);
         }
      }
      catch (Exception e) {
         e.printStackTrace();
      }
   }

   /**
    * Lists recursive all files to modify.
    * @param current The current file or folder.
    * @param filter The {@link FileFilter} to use.
    * @param filesToModify The {@link File} {@link List} to fill with the found files.
    */
   public static void listFiles(File current, FileFilter filter, List<File> filesToModify) {
      if (current.isFile()) {
         if (filter.accept(current)) { // Double checked because maybe the initial path is already a file.
            filesToModify.add(current);
         }
      }
      else {
         File[] subs = current.listFiles(filter);
         if (subs != null) {
            for (File sub : subs) {
               listFiles(sub, filter, filesToModify);
            }
         }
      }
   }
   
   /**
    * Computes the new file content.
    * @param content The old content.
    * @param oldHeader The old header to replace.
    * @param newHeader The new header to add.
    * @return The computed new content.
    */
   protected static String computeNewContent(String content, String oldHeader, String newHeader) {
      // Remove white space;
      content = content.trim();
      // Remove old header if required
      if (content.startsWith(oldHeader)) {
         content = content.substring(oldHeader.length()).trim();
      }
      // Return new content
      return newHeader + StringUtil.NEW_LINE + StringUtil.NEW_LINE + content;
   }
}
