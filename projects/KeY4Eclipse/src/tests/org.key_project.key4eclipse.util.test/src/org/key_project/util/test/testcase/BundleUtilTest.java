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

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import junit.framework.TestCase;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.junit.Test;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.Activator;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Contains tests for {@link BundleUtil}
 * @author Martin Hentschel
 */
public class BundleUtilTest extends TestCase {
   /**
    * Tests {@link BundleUtil#computeMD5(String, String)}.
    */
   @Test
   public void testComputeMD5() throws IOException {
      // Test null plugin
      try {
         BundleUtil.computeMD5(null, "data/HelloWorld.txt");
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("No plug-in defined.", e.getMessage());
      }
      // Test null file
      try {
         BundleUtil.computeMD5(Activator.PLUGIN_ID, null);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("No path in plug-in \"org.key_project.util.test\" defined.", e.getMessage());
      }
      // Test not existing bundle
      try {
         BundleUtil.computeMD5("NOT_EXISTING_BUNDLE", "data/HelloWorld.txt");
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Can't find plug-in \"NOT_EXISTING_BUNDLE\".", e.getMessage());
      }
      // Test not existing file
      try {
         BundleUtil.computeMD5(Activator.PLUGIN_ID, "data/NOT_EXISTING_FILE.txt");
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Can't find resource \"data/NOT_EXISTING_FILE.txt\" in plug-in \"org.key_project.util.test\".", e.getMessage());
      }
      // Test content
      assertEquals("b10a8db164e0754105b7a99be72e3fe5", BundleUtil.computeMD5(Activator.PLUGIN_ID, "data/HelloWorld.txt"));
   }

   /**
    * Tests {@link BundleUtil#extractFromBundleToFilesystem(String, String, java.io.File)}
    */
   @Test
   public void testExtractFromBundleToFilesystem() throws CoreException, IOException {
      File tmpDir = File.createTempFile("BundleUtilTest", "testExtractFromBundleToWorkspace_File");
      try {
         // Test not existing directory
         IOUtil.delete(tmpDir);
         BundleUtil.extractFromBundleToFilesystem(Activator.PLUGIN_ID, "data/extractTest", tmpDir);
         doTestExtractFromBundleToFilesystem(tmpDir);
         // Test existing directory
         IOUtil.delete(tmpDir);
         tmpDir.mkdirs();
         File additionalFolder = TestUtilsUtil.createFolder(new File(tmpDir, "EmptyAdditionalDir"));
         File additionalFile = TestUtilsUtil.createFile(new File(tmpDir, "AdditionalFile.txt"), "AdditionalFile");
         File existingFolder = TestUtilsUtil.createFolder(new File(tmpDir, "SubFolder"));
         File existingFile = TestUtilsUtil.createFile(new File(tmpDir, "File.txt"), "ReplacedContent");
         BundleUtil.extractFromBundleToFilesystem(Activator.PLUGIN_ID, "data/extractTest", tmpDir);
         doTestExtractFromBundleToFilesystem(tmpDir);
         assertTrue(additionalFolder.exists());
         assertTrue(additionalFolder.isDirectory());
         assertTrue(additionalFile.exists());
         assertTrue(additionalFile.isFile());
         assertEquals("AdditionalFile", IOUtil.readFrom(new FileInputStream(additionalFile)));
         assertTrue(existingFolder.exists());
         assertTrue(existingFolder.isDirectory());
         assertTrue(existingFile.exists());
         assertTrue(existingFile.isFile());
         assertEquals("File", IOUtil.readFrom(new FileInputStream(existingFile)));
         // Test null plugin-id
         try {
            BundleUtil.extractFromBundleToFilesystem(null, "data/extractTest", tmpDir);
            fail("Exception expected.");
         }
         catch (CoreException e) {
             assertEquals("No plug-in ID defined.", e.getMessage());
         }
         // Test invalid plugin-id
         try {
            BundleUtil.extractFromBundleToFilesystem("INVALID", "data/extractTest", tmpDir);
            fail("Exception expected.");
         }
         catch (CoreException e) {
             assertEquals("Can't find plug-in with ID \"INVALID\".", e.getMessage());
         }
         // Test null path
         try {
             BundleUtil.extractFromBundleToFilesystem(Activator.PLUGIN_ID, null, tmpDir);
             fail("Exception expected.");
         }
         catch (CoreException e) {
             assertEquals("No path in plug-in defined.", e.getMessage());
         }
         // Test null target
         try {
             BundleUtil.extractFromBundleToFilesystem(Activator.PLUGIN_ID, "data/extractTest", null);
             fail("Exception expected.");
         }
         catch (CoreException e) {
             assertEquals("No target is defined.", e.getMessage());
         }
      }
      finally {
         IOUtil.delete(tmpDir);
      }
   }

   /**
    * Executes assertions to make sure that the correct files are extracted
    * for {@link #testExtractFromBundleToFilesystem()}. 
    * @param folder The target folder.
    * @throws IOException Occurred Exception
    */
   protected static void doTestExtractFromBundleToFilesystem(File folder) throws IOException {
      // Test container
      assertNotNull(folder);
      assertTrue(folder.exists());
      assertTrue(folder.isDirectory());
      // Test container/File.txt
      File file = new File(folder, "File.txt");
      assertTrue(file.exists());
      assertTrue(file.isFile());
      assertEquals("File", IOUtil.readFrom(new FileInputStream(file)));
      // Test container/EmptyFolder
      // Test container/SubFolder
      File subFolder = new File(folder, "SubFolder");
      assertTrue(subFolder.exists());
      assertTrue(subFolder.isDirectory());
      // Test container/SubFolder/EmptySubFolder
      // Test container/SubFolder/SubSubFolder
      File subSubFolder = new File(subFolder, "SubSubFolder");
      assertTrue(subSubFolder.exists());
      assertTrue(subSubFolder.isDirectory());
      // Test container/SubFolder/SubSubFolder/EmptySubSubFolder
      // Test container/SubFolder/SubSubFolder/SubSubFile.txt
      File subSubFile = new File(subSubFolder, "SubSubFile.txt");
      assertTrue(subSubFile.exists());
      assertTrue(subSubFile.isFile());
      assertEquals("SubSubFile", IOUtil.readFrom(new FileInputStream(subSubFile)));
      // Test container/SubFolder/SubFile.txt
      File subFile = new File(subFolder, "SubFile.txt");
      assertTrue(subFile.exists());
      assertTrue(subFile.isFile());
      assertEquals("SubFile", IOUtil.readFrom(new FileInputStream(subFile)));
   }
    
   /**
    * Tests {@link BundleUtil#openInputStream(String, String)}
    */
   @Test
   public void testOpenInputStream() throws IOException {
       InputStream in = null;
       try {
          // Test valid resource
          in = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/extractTest/File.txt");
          assertEquals("File", IOUtil.readFrom(in));
          in.close();
          // Test invalid resource in valid plug-in
          try {
              BundleUtil.openInputStream(Activator.PLUGIN_ID, "INVALID");
              fail("Opening an invalid resource should not be possible.");
          }
          catch (IOException e) {
              assertEquals("Can't find resource \"INVALID\" in plug-in \"" + Activator.PLUGIN_ID + "\".", e.getMessage());
          }
          // Test null path
          try {
              BundleUtil.openInputStream(Activator.PLUGIN_ID, null);
              fail("Opening an invalid resource should not be possible.");
          }
          catch (IOException e) {
              assertEquals("No path in plug-in \"" + Activator.PLUGIN_ID + "\" defined.", e.getMessage());
          }
          // Test invalid plug-in
          try {
              BundleUtil.openInputStream("INVALID", "data/extractTest/File.txt");
              fail("Opening a resource in an invalid plug-in should not be possible.");
          }
          catch (IOException e) {
              assertEquals("Can't find plug-in \"INVALID\".", e.getMessage());
          }
          // Test null plug-in
          try {
              BundleUtil.openInputStream(null, "data/extractTest/File.txt");
              fail("Opening a resource in an invalid plug-in should not be possible.");
          }
          catch (IOException e) {
              assertEquals("No plug-in defined.", e.getMessage());
          }
       }
       finally {
           if (in != null) {
               in.close();
           }
       }
   }
   
   /**
    * Tests {@link BundleUtil#extractFromBundleToWorkspace(String, String, org.eclipse.core.resources.IContainer)}
    */
   @Test
   public void testExtractFromBundleToWorkspace() throws IOException, CoreException {
      // Create projects
      IProject project1 = TestUtilsUtil.createProject("BundleUtilTest_testExtractFromBundleToWorkspace_1");
      IProject project2 = TestUtilsUtil.createProject("BundleUtilTest_testExtractFromBundleToWorkspace_2");
      // Create folder
      IFolder emptyFolder = TestUtilsUtil.createFolder(project2, "emptyFolder");
      IFolder subFolder = TestUtilsUtil.createFolder(project2, "subFolder");
      IFolder subSubFolder = TestUtilsUtil.createFolder(subFolder, "subSubFolder");
      // Extract to existing project
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", project1);
      doTestExtractFromBundleToFilesystem(project1);
      // Extract to existing emptyFolder
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", emptyFolder);
      doTestExtractFromBundleToFilesystem(emptyFolder);
      // Extract to existing subSubFolder
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", subSubFolder);
      doTestExtractFromBundleToFilesystem(subSubFolder);
      // Extract to not existing project
      IProject project3 = ResourcesPlugin.getWorkspace().getRoot().getProject("BundleUtilTest_testExtractFromBundleToWorkspace_3");
      assertFalse(project3.exists());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", project3);
      doTestExtractFromBundleToFilesystem(project3);
      assertTrue(project3.exists());
      assertTrue(project3.isOpen());
      // Extract to not existing folder
      IFolder folder = project3.getFolder("NotExisting");
      assertFalse(folder.exists());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", folder);
      doTestExtractFromBundleToFilesystem(folder);
      assertTrue(folder.exists());
      // Test null plugin-id
      try {
         BundleUtil.extractFromBundleToWorkspace(null, "data/extractTest", project1);
         fail("Exception expected.");
      }
      catch (CoreException e) {
          assertEquals("No plug-in ID defined.", e.getMessage());
      }
      // Test invalid plugin-id
      try {
         BundleUtil.extractFromBundleToWorkspace("INVALID", "data/extractTest", project1);
         fail("Exception expected.");
      }
      catch (CoreException e) {
          assertEquals("Can't find plug-in with ID \"INVALID\".", e.getMessage());
      }
      // Test null path
      try {
          BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, null, project1);
          fail("Exception expected.");
      }
      catch (CoreException e) {
          assertEquals("No path in plug-in defined.", e.getMessage());
      }
      // Test null target
      try {
          BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", null);
          fail("Exception expected.");
      }
      catch (CoreException e) {
          assertEquals("No target is defined.", e.getMessage());
      }
   }

   /**
    * Executes assertions to make sure that the correct files are extracted
    * for {@link #testExtractFromBundleToWorkspace()}. 
    * @param container The target container.
    * @throws IOException Occurred Exception
    * @throws CoreException Occurred Exception
    */
   protected static void doTestExtractFromBundleToFilesystem(IContainer container) throws IOException, CoreException {
      // Test container
      assertNotNull(container);
      assertTrue(container.exists());
      // Test container/File.txt
      assertNotNull(container.getFile(new Path("File.txt")));
      assertTrue(container.getFile(new Path("File.txt")).exists());
      assertEquals("File", IOUtil.readFrom(container.getFile(new Path("File.txt")).getContents()));
      // Test container/EmptyFolder
      // Test container/SubFolder
      assertNotNull(container.getFolder(new Path("SubFolder")));
      assertTrue(container.getFolder(new Path("SubFolder")).exists());
      // Test container/SubFolder/EmptySubFolder
      // Test container/SubFolder/SubSubFolder
      assertNotNull(container.getFolder(new Path("SubFolder/SubSubFolder")));
      assertTrue(container.getFolder(new Path("SubFolder/SubSubFolder")).exists());
      // Test container/SubFolder/SubSubFolder/EmptySubSubFolder
      // Test container/SubFolder/SubSubFolder/SubSubFile.txt
      assertNotNull(container.getFile(new Path("SubFolder/SubSubFolder/SubSubFile.txt")));
      assertTrue(container.getFile(new Path("SubFolder/SubSubFolder/SubSubFile.txt")).exists());
      assertEquals("SubSubFile", IOUtil.readFrom(container.getFile(new Path("SubFolder/SubSubFolder/SubSubFile.txt")).getContents()));      
      // Test container/SubFolder/SubFile.txt
      assertNotNull(container.getFile(new Path("SubFolder/SubFile.txt")));
      assertTrue(container.getFile(new Path("SubFolder/SubFile.txt")).exists());
      assertEquals("SubFile", IOUtil.readFrom(container.getFile(new Path("SubFolder/SubFile.txt")).getContents()));      
   }
}