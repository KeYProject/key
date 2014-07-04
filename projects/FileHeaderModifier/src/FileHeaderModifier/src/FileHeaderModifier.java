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
      modifySystem();
      modifyProjects();
   }
 
   /**
    * Updates the header of all files in the "projects" folder of the KeY repository. 
    */
   protected static void modifyProjects() {
      File projectDir = new File("D:\\Forschung\\GIT\\KeY\\projects");
      File outputDir = new File("C:\\temp\\test_out");
      File oldHeaderFile = new File("data/ProjectsHeader.txt");
      File newHeaderFile = new File("data/ProjectsHeader.txt");
      modify(outputDir, oldHeaderFile, newHeaderFile, projectDir);
   }
   
   /**
    * Updates the header of all files in the "system" folder of the KeY repository. 
    */
   protected static void modifySystem() {
      File srcDir = new File("D:\\Forschung\\GIT\\KeY\\system\\src");
      File testDir = new File("D:\\Forschung\\GIT\\KeY\\system\\test");
      File outputDir = new File("C:\\temp\\test_out");
      File oldHeaderFile = new File("data/KeyHeader.txt");
      File newHeaderFile = new File("data/KeyHeader.txt");
      modify(outputDir, oldHeaderFile, newHeaderFile, srcDir, testDir);
   }
   
   /**
    * Updates the header of all files.
    * @param outputDir The output directory to write modified files to.
    * @param oldHeaderFile The old header.
    * @param newHeaderFile The new header.
    * @param workingDirs The directories to check files in. 
    */
   protected static void modify(File outputDir, 
                                File oldHeaderFile, // If old and new header is identical the header is only added to files if not already present
                                File newHeaderFile,
                                File... workingDirs) {
      try {
         // Define settings
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
                     return "data".equals(file.getName()) ||
                            "additionalUndeployedData".equals(file.getName());
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
         System.out.println("Working Directories: ");
         for (File workingDir : workingDirs) {
            System.out.println("   - " + workingDir);
         }
         System.out.println("Output Directory: " + outputDir);
         System.out.println("Old Header: File" + oldHeaderFile);
         System.out.println("New Header File: " + newHeaderFile);
         System.out.println();
         List<File> modifiedFiles = new LinkedList<File>();
         for (File workingDir : workingDirs) {
            // Test settings
            if (workingDir.equals(outputDir)) {
               throw new IllegalArgumentException("Working and Output Directory are the same.");
            }
            // List files to modify
            List<File> filesToModify = new LinkedList<File>();
            listFiles(workingDir, filter, filesToModify);
            // Read headers
            String oldHeader = oldHeaderFile != null ? IOUtil.readFrom(oldHeaderFile).trim() : null;
            String newHeader = newHeaderFile != null ? IOUtil.readFrom(newHeaderFile).trim() : null;
            // Modify files and write result to output directory
            for (File oldFile : filesToModify) {
               // Read old content
               String oldContent = IOUtil.readFrom(oldFile).trim();
               // Check if it is required to modify the file
               if (!oldContent.startsWith(newHeader)) {
                  // Write current file into console
                  System.out.println("Modifying: " + oldFile);
                  // Compute new content
                  String newContent = computeNewContent(oldContent, oldHeader, newHeader);
                  // Compute file in output dir
                  int prefixLength = workingDir.getParent().length();
                  String path = oldFile.toString().substring(prefixLength); 
                  File newFile = new File(outputDir, path);
                  // Make sure that outputDir exists
                  if (!newFile.getParentFile().exists()) {
                     newFile.getParentFile().mkdirs();
                  }
                  // Create file in outputDir (Existing files will be overwritten)
                  IOUtil.writeTo(newFile, newContent);
                  modifiedFiles.add(oldFile);
               }
            }
         }
         // Print number of modified files
         System.out.println();
         System.out.println(modifiedFiles.size() + " files modified.");
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
    * @param oldHeader The optional old header to replace.
    * @param newHeader The optional new header to add.
    * @return The computed new content.
    */
   protected static String computeNewContent(String content, String oldHeader, String newHeader) {
      // Remove old header if required
      if (oldHeader != null && content.startsWith(oldHeader)) {
         content = content.substring(oldHeader.length()).trim();
      }
      // Addd new header if required
      if (newHeader != null) {
         content = newHeader + StringUtil.NEW_LINE + StringUtil.NEW_LINE + content;
      }
      // Return new content
      return content;
   }
}