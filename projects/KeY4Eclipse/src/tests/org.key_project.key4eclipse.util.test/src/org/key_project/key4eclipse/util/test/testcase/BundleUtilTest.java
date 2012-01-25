/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.test.testcase;

import java.io.IOException;

import junit.framework.TestCase;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.key4eclipse.util.java.IOUtil;
import org.key_project.key4eclipse.util.test.Activator;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;

/**
 * Contains tests for {@link BundleUtil}
 * @author Martin Hentschel
 */
public class BundleUtilTest extends TestCase {
   /**
    * Tests {@link BundleUtil#extractFromBundleToWorkspace(String, String, org.eclipse.core.resources.IContainer)}
    */
   @Test
   public void testExtractFromBundleToWorkspace() {
      try {
         // Create projects
         IProject project1 = TestUtilsUtil.createProject("BundleUtilTest_testExtractFromBundleToWorkspace_1");
         IProject project2 = TestUtilsUtil.createProject("BundleUtilTest_testExtractFromBundleToWorkspace_2");
         // Create folder
         IFolder emptyFolder = TestUtilsUtil.createFolder(project2, "emptyFolder");
         IFolder subFolder = TestUtilsUtil.createFolder(project2, "subFolder");
         IFolder subSubFolder = TestUtilsUtil.createFolder(subFolder, "subSubFolder");
         // Extract to project
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", project1);
         doTestExtractFromBundleToWorkspace(project1);
         // Extract to emptyFolder
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", emptyFolder);
         doTestExtractFromBundleToWorkspace(emptyFolder);
         // Extract to subSubFolder
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/extractTest", subSubFolder);
         doTestExtractFromBundleToWorkspace(subSubFolder);
      }
      catch (Exception e) {
         e.printStackTrace();
         fail();
      }
   }

   /**
    * Executes assertions to make sure that the correct files are extracted
    * for {@link #testExtractFromBundleToWorkspace()}. 
    * @param container The target container.
    * @throws IOException Occurred Exception
    * @throws CoreException Occurred Exception
    */
   protected static void doTestExtractFromBundleToWorkspace(IContainer container) throws IOException, CoreException {
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
