package org.key_project.key4eclipse.util.test.testcase;

import java.io.File;
import java.io.IOException;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.ResourceUtil;
import org.key_project.key4eclipse.util.java.ArrayUtil;
import org.key_project.key4eclipse.util.java.StringUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;

/**
 * Contains tests for {@link ResourceUtil}
 * @author Martin Hentschel
 */
public class ResourceUtilTest extends TestCase {
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
