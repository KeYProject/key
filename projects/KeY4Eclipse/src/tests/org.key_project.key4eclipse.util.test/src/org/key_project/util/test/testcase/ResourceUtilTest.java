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

package org.key_project.util.test.testcase;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.ResourceUtil.IFileOpener;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Contains tests for {@link ResourceUtil}
 * @author Martin Hentschel
 */
public class ResourceUtilTest extends TestCase {
   /**
    * Tests {@link ResourceUtil#copyIntoWorkspace(org.eclipse.core.resources.IContainer, File...)}.
    */
   @Test
   public void testCopyIntoWorkspace() throws Exception {
      // Create project
      IProject project = TestUtilsUtil.createProject("ResourceUtilTest_testCopyIntoWorkspace");
      IFile projectFile = project.getFile(".project");
      assertTrue(projectFile.exists());
      assertEquals(1, project.members().length); // .project file
      IFolder notExistingFolder = project.getFolder("NotExisting");
      assertFalse(notExistingFolder.exists());
      // Create files to copy in a temporary directory
      File tempDir = IOUtil.createTempDirectory("ResourceUtilTest", "testCopyIntoWorkspace");
      try {
         new File(tempDir, "emptyFolder").mkdirs();
         IOUtil.writeTo(new FileOutputStream(new File(tempDir, "Text.txt")), "Text.txt");
         File subDir = new File(tempDir, "subFolder");
         subDir.mkdirs();
         IOUtil.writeTo(new FileOutputStream(new File(subDir, "SubFile.txt")), "SubFile.txt");
         File subSubDir = new File(subDir, "subSubFolder");
         subSubDir.mkdirs();
         IOUtil.writeTo(new FileOutputStream(new File(subSubDir, "SubSubFileA.txt")), "SubSubFileA.txt");
         IOUtil.writeTo(new FileOutputStream(new File(subSubDir, "SubSubFileB.txt")), "SubSubFileB.txt");
         // Test null target
         try {
            ResourceUtil.copyIntoWorkspace(null, null, tempDir);
            fail("Exception expected");
         }
         catch (Exception e) {
            assertEquals("Target not defined.", e.getMessage());
         }
         // Test not existing target
         try {
            ResourceUtil.copyIntoWorkspace(notExistingFolder, null, tempDir);
            fail("Exception expected");
         }
         catch (Exception e) {
            assertEquals("Target \"" + notExistingFolder + "\" does not exist.", e.getMessage());
         }
         // Test null source
         ResourceUtil.copyIntoWorkspace(project, null, (File[])null);
         ResourceUtil.copyIntoWorkspace(project, null, (File)null);
         assertEquals(1, project.members().length); // .project file
         assertTrue(projectFile.exists());
         // Copy initial content
         ResourceUtil.copyIntoWorkspace(project, null, tempDir.listFiles());
         assertEquals(4, project.members().length);
         assertTrue(projectFile.exists());
         IFolder targetEmptyFolder = project.getFolder("emptyFolder");
         assertTrue(targetEmptyFolder.exists());
         assertEquals(0, targetEmptyFolder.members().length);
         IFile targetText = project.getFile("Text.txt");
         assertEquals("Text.txt", ResourceUtil.readFrom(targetText));
         IFolder targetSubDir = project.getFolder("subFolder");
         assertTrue(targetSubDir.exists());
         assertEquals(2, targetSubDir.members().length);
         IFile targetSubFile = targetSubDir.getFile("SubFile.txt");
         assertEquals("SubFile.txt", ResourceUtil.readFrom(targetSubFile));
         IFolder targetSubSubDir = targetSubDir.getFolder("subSubFolder"); 
         assertTrue(targetSubSubDir.exists());
         assertEquals(2, targetSubSubDir.members().length);
         IFile targetSubSubFileA = targetSubSubDir.getFile("SubSubFileA.txt");
         assertEquals("SubSubFileA.txt", ResourceUtil.readFrom(targetSubSubFileA));
         IFile targetSubSubFileB = targetSubSubDir.getFile("SubSubFileB.txt");
         assertEquals("SubSubFileB.txt", ResourceUtil.readFrom(targetSubSubFileB));
         // Prepare temporary directory for adding new files and folders
         IOUtil.delete(tempDir);
         new File(tempDir, "newEmptyFolder").mkdirs();
         IOUtil.writeTo(new FileOutputStream(new File(tempDir, "NewText.txt")), "NewText.txt");
         File newSubDir = new File(tempDir, "newSubFolder");
         newSubDir.mkdirs();
         IOUtil.writeTo(new FileOutputStream(new File(newSubDir, "NewSubFile.txt")), "NewSubFile.txt");
         // Add new content
         ResourceUtil.copyIntoWorkspace(project, null, tempDir.listFiles());
         assertEquals(7, project.members().length);
         assertTrue(projectFile.exists());
         assertTrue(targetEmptyFolder.exists());
         assertEquals(0, targetEmptyFolder.members().length);
         assertEquals("Text.txt", ResourceUtil.readFrom(targetText));
         assertTrue(targetSubDir.exists());
         assertEquals(2, targetSubDir.members().length);
         assertEquals("SubFile.txt", ResourceUtil.readFrom(targetSubFile));
         assertTrue(targetSubSubDir.exists());
         assertEquals(2, targetSubSubDir.members().length);
         assertEquals("SubSubFileA.txt", ResourceUtil.readFrom(targetSubSubFileA));
         assertEquals("SubSubFileB.txt", ResourceUtil.readFrom(targetSubSubFileB));
         IFolder targetNewEmptyFolder = project.getFolder("newEmptyFolder");
         assertTrue(targetNewEmptyFolder.exists());
         assertEquals(0, targetNewEmptyFolder.members().length);
         IFile targetNewText = project.getFile("NewText.txt");
         assertEquals("NewText.txt", ResourceUtil.readFrom(targetNewText));
         IFolder targetNewSubDir = project.getFolder("newSubFolder");
         assertTrue(targetNewSubDir.exists());
         assertEquals(1, targetNewSubDir.members().length);
         IFile targetNewSubFile = targetNewSubDir.getFile("NewSubFile.txt");
         assertEquals("NewSubFile.txt", ResourceUtil.readFrom(targetNewSubFile));
         // Prepare temporary directory for replacing files
         newSubDir = new File(tempDir, "newSubFolder");
         newSubDir.mkdirs();
         IOUtil.writeTo(new FileOutputStream(new File(newSubDir, "NewSubFile.txt")), "NewSubFile-Changed.txt");
         IOUtil.writeTo(new FileOutputStream(new File(tempDir, "Text.txt")), "Text-Changed.txt");
         // Replace some files
         ResourceUtil.copyIntoWorkspace(project, null, tempDir.listFiles());
         assertEquals(7, project.members().length);
         assertTrue(projectFile.exists());
         assertTrue(targetEmptyFolder.exists());
         assertEquals(0, targetEmptyFolder.members().length);
         assertEquals("Text-Changed.txt", ResourceUtil.readFrom(targetText));
         assertTrue(targetSubDir.exists());
         assertEquals(2, targetSubDir.members().length);
         assertEquals("SubFile.txt", ResourceUtil.readFrom(targetSubFile));
         assertTrue(targetSubSubDir.exists());
         assertEquals(2, targetSubSubDir.members().length);
         assertEquals("SubSubFileA.txt", ResourceUtil.readFrom(targetSubSubFileA));
         assertEquals("SubSubFileB.txt", ResourceUtil.readFrom(targetSubSubFileB));
         assertTrue(targetNewEmptyFolder.exists());
         assertEquals(0, targetNewEmptyFolder.members().length);
         assertEquals("NewText.txt", ResourceUtil.readFrom(targetNewText));
         assertTrue(targetNewSubDir.exists());
         assertEquals(1, targetNewSubDir.members().length);
         assertEquals("NewSubFile-Changed.txt", ResourceUtil.readFrom(targetNewSubFile));
         // Replace some files with a custom opener
         IFileOpener opener = new IFileOpener() {
            @Override
            public InputStream open(File file) throws IOException {
               String content = IOUtil.readFrom(file);
               content += "-Modified";
               return new ByteArrayInputStream(content.getBytes());
            }
         };
         ResourceUtil.copyIntoWorkspace(project, opener, tempDir.listFiles());
         assertEquals(7, project.members().length);
         assertTrue(projectFile.exists());
         assertTrue(targetEmptyFolder.exists());
         assertEquals(0, targetEmptyFolder.members().length);
         assertEquals("Text-Changed.txt-Modified", ResourceUtil.readFrom(targetText));
         assertTrue(targetSubDir.exists());
         assertEquals(2, targetSubDir.members().length);
         assertEquals("SubFile.txt", ResourceUtil.readFrom(targetSubFile));
         assertTrue(targetSubSubDir.exists());
         assertEquals(2, targetSubSubDir.members().length);
         assertEquals("SubSubFileA.txt", ResourceUtil.readFrom(targetSubSubFileA));
         assertEquals("SubSubFileB.txt", ResourceUtil.readFrom(targetSubSubFileB));
         assertTrue(targetNewEmptyFolder.exists());
         assertEquals(0, targetNewEmptyFolder.members().length);
         assertEquals("NewText.txt-Modified", ResourceUtil.readFrom(targetNewText));
         assertTrue(targetNewSubDir.exists());
         assertEquals(1, targetNewSubDir.members().length);
         assertEquals("NewSubFile-Changed.txt-Modified", ResourceUtil.readFrom(targetNewSubFile));
      }
      finally {
         System.out.println(tempDir);
         IOUtil.delete(tempDir);
      }
   }
   
   /**
    * Tests {@link ResourceUtil#readFrom(IFile)}
    * @throws Exception
    */
   @Test
   public void testReadFrom() throws Exception {
      // Create project and file
      IProject project = TestUtilsUtil.createProject("ResourceUtilTest_testReadFrom");
      IFile file = TestUtilsUtil.createFile(project, "file.txt", "Hello World!");
      IFile notExisting = project.getFile("NotExistingFile.txt");
      assertFalse(notExisting.exists());
      // Test reading
      assertNull(ResourceUtil.readFrom(null));
      assertNull(ResourceUtil.readFrom(notExisting));
      assertEquals("Hello World!", ResourceUtil.readFrom(file));
   }
   
   /**
    * Tests {@link ResourceUtil#createFile(IFile, java.io.InputStream, org.eclipse.core.runtime.IProgressMonitor)}.
    */
   @Test
   public void testCreateFile() throws Exception {
      // Create project
      IProject project = TestUtilsUtil.createProject("ResourceUtilTest_testCreateFile");
      IFile toCreate = project.getFile("NewFile.txt");
      assertFalse(toCreate.exists());
      // Test null
      ResourceUtil.createFile(null, null, null);
      assertFalse(toCreate.exists());
      // Create file
      ResourceUtil.createFile(toCreate, new ByteArrayInputStream("Hello".getBytes()), null);
      assertTrue(toCreate.exists());
      assertEquals("Hello", ResourceUtil.readFrom(toCreate));
      // Change content of file
      ResourceUtil.createFile(toCreate, new ByteArrayInputStream("Changed".getBytes()), null);
      assertTrue(toCreate.exists());
      assertEquals("Changed", ResourceUtil.readFrom(toCreate));
      // Change content to null
      ResourceUtil.createFile(toCreate, null, null);
      assertTrue(toCreate.exists());
      assertEquals("", ResourceUtil.readFrom(toCreate));
      // Change content of file again
      ResourceUtil.createFile(toCreate, new ByteArrayInputStream("Changed Again".getBytes()), null);
      assertTrue(toCreate.exists());
      assertEquals("Changed Again", ResourceUtil.readFrom(toCreate));
      // Delete file
      toCreate.delete(true, null);
      assertFalse(toCreate.exists());
      // Create file again with null
      ResourceUtil.createFile(toCreate, null, null);
      assertTrue(toCreate.exists());
      assertEquals("", ResourceUtil.readFrom(toCreate));
      // Change content of file
      ResourceUtil.createFile(toCreate, new ByteArrayInputStream("Content".getBytes()), null);
      assertTrue(toCreate.exists());
      assertEquals("Content", ResourceUtil.readFrom(toCreate));
   }
   
   /**
    * Tests {@link ResourceUtil#getFileNameWithoutExtension(IFile)}.
    */
   @Test
   public void testGetFileNameWithoutExtension() {
      IProject project = TestUtilsUtil.createProject("ResourceUtilTest_testGetFileNameWithoutExtension");
      assertNull(ResourceUtil.getFileNameWithoutExtension(null));
      assertEquals("test", ResourceUtil.getFileNameWithoutExtension(project.getFile("test.txt")));
      assertEquals("hello.world", ResourceUtil.getFileNameWithoutExtension(project.getFile("hello.world.diagram")));
      assertEquals("", ResourceUtil.getFileNameWithoutExtension(project.getFile(".project")));
      assertEquals("file", ResourceUtil.getFileNameWithoutExtension(project.getFile("file")));
   }
   
   /**
    * Tests {@link ResourceUtil#getProject(String)}.
    */
   @Test
   public void testGetProject() {
      // Create example projects
      IProject project1 = TestUtilsUtil.createProject("ResourceUtilTest_testGetProject1");
      IProject project2 = TestUtilsUtil.createProject("ResourceUtilTest_testGetProject2");
      // Test null
      assertNull(ResourceUtil.getProject(null));
      // Test empty
      assertNull(ResourceUtil.getProject(StringUtil.EMPTY_STRING));
      // Test invalid
      IProject invalid = ResourceUtil.getProject("INVALID"); 
      assertNotNull(invalid);
      assertFalse(invalid.exists());
      assertFalse(invalid.isOpen());
      // Test valid
      assertEquals(project1, ResourceUtil.getProject(project1.getName()));
      assertEquals(project2, ResourceUtil.getProject(project2.getName()));
   }
    
   /**
    * Tests {@link ResourceUtil#findResourceForLocation(File)}
    */
   @Test
   public void testFindResourceForLocation() throws CoreException, IOException {
      // Create temp file
      File tempFile = null;
      try {
         tempFile = File.createTempFile("Test", ".txt");
         // Create project
         IProject project = TestUtilsUtil.createProject("ResourceUtilTest_testfindResource");
         IFolder folder = TestUtilsUtil.createFolder(project, "emptyFolder");
         File location = ResourceUtil.getLocation(folder);
         IFile file = TestUtilsUtil.createFile(project, "Test.txt", "Hello World!");
         File fileLocation = ResourceUtil.getLocation(file);
         // Test null
         IResource[] result = ResourceUtil.findResourceForLocation(null);
         assertNotNull(result);
         assertEquals(0, result.length);
         // Text existing location
         result = ResourceUtil.findResourceForLocation(location);
         assertNotNull(result);
         assertEquals(1, result.length);
         assertEquals(folder, result[0]);
         // Text existing file location
         result = ResourceUtil.findResourceForLocation(fileLocation);
         assertNotNull(result);
         assertEquals(1, result.length);
         assertEquals(file, result[0]);
         // Test not existing location
         result = ResourceUtil.findResourceForLocation(new File("INVALID"));
         assertNotNull(result);
         assertEquals(0, result.length);
         // Test existing location which is not part of the workspace
         result = ResourceUtil.findResourceForLocation(tempFile.getParentFile());
         assertNotNull(result);
         assertEquals(0, result.length);
         // Test existing file location which is not part of the workspace
         result = ResourceUtil.findResourceForLocation(tempFile);
         assertNotNull(result);
         assertEquals(0, result.length);
      }
      finally {
         if (tempFile != null) {
            tempFile.delete();
         }
      }
   }

   /**
    * Tests {@link ResourceUtil#getLocation(org.eclipse.core.resources.IResource)}
    */
   @Test
   public void testGetLocation() {
      // Create project
      IProject project = TestUtilsUtil.createProject("ResourceUtilTest_testGetLocation");
      IFolder folder = TestUtilsUtil.createFolder(project, "emptyFolder");
      IFile file = TestUtilsUtil.createFile(project, "file.txt", "Hello World!");
      IFolder subfolder = TestUtilsUtil.createFolder(project, "subFolder");
      IFolder subFolderFolder = TestUtilsUtil.createFolder(subfolder, "emptyFolderInSubfolder");
      IFile subFolderFile = TestUtilsUtil.createFile(subfolder, "fileInSubfolder.txt", "Hello World!");
      // test null
      assertNull(ResourceUtil.getLocation(null));
      // test project
      File projectLocation = ResourceUtil.getLocation(project);
      assertNotNull(projectLocation);
      assertTrue(projectLocation.exists() && projectLocation.isDirectory());
      // test folder
      File folderLocation = ResourceUtil.getLocation(folder);
      assertNotNull(folderLocation);
      assertTrue(folderLocation.exists() && folderLocation.isDirectory());
      assertTrue(ArrayUtil.contains(projectLocation.listFiles(), folderLocation));
      // test file
      File fileLocation = ResourceUtil.getLocation(file);
      assertNotNull(fileLocation);
      assertTrue(fileLocation.exists() && fileLocation.isFile());
      assertTrue(ArrayUtil.contains(projectLocation.listFiles(), fileLocation));
      // test subfolder
      File subfolderLocation = ResourceUtil.getLocation(subfolder);
      assertNotNull(subfolderLocation);
      assertTrue(subfolderLocation.exists() && subfolderLocation.isDirectory());
      assertTrue(ArrayUtil.contains(projectLocation.listFiles(), subfolderLocation));
      // test subFolderFolder
      File subFolderFolderLocation = ResourceUtil.getLocation(subFolderFolder);
      assertNotNull(subFolderFolderLocation);
      assertTrue(subFolderFolderLocation.exists() && subFolderFolderLocation.isDirectory());
      assertTrue(ArrayUtil.contains(subfolderLocation.listFiles(), subFolderFolderLocation));
      // test subFolderFile
      File subFolderFileLocation = ResourceUtil.getLocation(subFolderFile);
      assertNotNull(subFolderFileLocation);
      assertTrue(subFolderFileLocation.exists() && subFolderFileLocation.isFile());
      assertTrue(ArrayUtil.contains(subfolderLocation.listFiles(), subFolderFileLocation));
   }
}
