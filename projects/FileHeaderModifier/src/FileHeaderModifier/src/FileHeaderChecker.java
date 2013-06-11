/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
      checkSystem();
      checkProjects();
   }
   
   /**
    * Lists all files with different header in the "projects" folder of the KeY repository.
    */
   protected static void checkProjects() {
      File projectDir = new File("D:\\Forschung\\GIT\\KeY\\projects");
      File headerFile = new File("data/ProjectsHeader.txt");
      check(headerFile, projectDir);
   }
   
   /**
    * Lists all files with different header in the "system" folder of the KeY repository.
    */
   protected static void checkSystem() {
      File srcDir = new File("D:\\Forschung\\GIT\\KeY\\system\\src");
      File testDir = new File("D:\\Forschung\\GIT\\KeY\\system\\test");
      File headerFile = new File("data/KeyHeader.txt");
      check(headerFile, srcDir, testDir);
   }
   
   /**
    * Lists all files with different header.
    * @param headerFile The header.
    * @param workingDirs The directories to check.
    */
   protected static void check(File headerFile, File... workingDirs) {
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
                  return true;
               }
            }
         };
         // Write settings into console
         System.out.println("Working Directories: " + workingDirs);
         System.out.println("New Header File: " + headerFile);
         System.out.println();
         // List files to check
         List<File> filesToModify = new LinkedList<File>();
         for (File workingDir : workingDirs) {
            FileHeaderModifier.listFiles(workingDir, filter, filesToModify);
         }
         // Read headers
         String newHeader = IOUtil.readFrom(headerFile).trim();
         // List files without header
         List<File> foundFiles = new LinkedList<File>();
         for (File file : filesToModify) {
            // Check if content starts with header
            String content = IOUtil.readFrom(file).trim();
            if (!content.startsWith(newHeader)) {
               foundFiles.add(file);
            }
         }
         // Print found files
         for (File file : foundFiles) {
            System.out.println("Missing Header: " + file);
         }
         // Print number of found files
         System.out.println();
         System.out.println(foundFiles.size() + " files found.");
      }
      catch (Exception e) {
         e.printStackTrace();
      }
   }
}