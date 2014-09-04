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

package org.key_project.key4eclipse.resources.test.testcase.junit;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.eclipse.BundleUtil;

public class AutoDeleteTests extends AbstractResourceTest {
   
   //Full build - single thread
   @Test
   public void testFullBuildSingleThreadAddAndRemoveJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildSingleThreadAddAndRemoveJavaFile", true, false, false, 1, true, false);
      testAddAndRemoveJavaFile(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadAddJavaFileAndRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildSingleThreadAddJavaFileAndRemoveMethod", true, false, false, 1, true, false);
      testAddJavaFileAndRemoveMethod(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadAddJavaFileAndRemoveAllMethods() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildSingleThreadAddJavaFileAndRemoveAllMethods", true, false, false, 1, true, false);
      testAddJavaFileAndRemoveAllMethods(project);
      project.close(null);
   }

   @Test
   public void testFullBuildSingleThreadAddSomeFilesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildSingleThreadAddSomeFilesAndRemoveOne", true, false, false, 1, true, false);
      testAddSomeFilesAndRemoveOne(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadAddPackagesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildSingleThreadAddPackagesAndRemoveOne", true, false, false, 1, true, false);
      testAddPackagesAndRemoveOne(project);
      project.close(null);
   }
   
   
   //Full build - multiple threads
   @Test
   public void testFullBuildMultipleThreadsAddAndRemoveJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildMultipleThreadsAddAndRemoveJavaFile", true, false, true, 2, true, false);
      testAddAndRemoveJavaFile(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsAddJavaFileAndRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildMultipleThreadsAddJavaFileAndRemoveMethod", true, false, true, 2, true, false);
      testAddJavaFileAndRemoveMethod(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsAddJavaFileAndRemoveAllMethods() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildMultipleThreadsAddJavaFileAndRemoveAllMethods", true, false, true, 2, true, false);
      testAddJavaFileAndRemoveAllMethods(project);
      project.close(null);
   }

   @Test
   public void testFullBuildMultipleThreadsAddSomeFilesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildMultipleThreadsAddSomeFilesAndRemoveOne", true, false, true, 2, true, false);
      testAddSomeFilesAndRemoveOne(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsAddPackagesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testFullBuildMultipleThreadsAddPackagesAndRemoveOne", true, false, true, 2, true, false);
      testAddPackagesAndRemoveOne(project);
      project.close(null);
   }
   
   
   //Efficient build - single thread
   @Test
   public void testEfficientBuildSingleThreadAddAndRemoveJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildSingleThreadAddAndRemoveJavaFile", true, true, false, 1, true, false);
      testAddAndRemoveJavaFile(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadAddJavaFileAndRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildSingleThreadAddJavaFileAndRemoveMethod", true, true, false, 1, true, false);
      testAddJavaFileAndRemoveMethod(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadAddJavaFileAndRemoveAllMethods() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildSingleThreadAddJavaFileAndRemoveAllMethods", true, true, false, 1, true, false);
      testAddJavaFileAndRemoveAllMethods(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildSingleThreadAddSomeFilesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildSingleThreadAddSomeFilesAndRemoveOne", true, true, false, 1, true, false);
      testAddSomeFilesAndRemoveOne(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadAddPackagesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildSingleThreadAddPackagesAndRemoveOne", true, true, false, 1, true, false);
      testAddPackagesAndRemoveOne(project);
      project.close(null);
   }
   
   
   //Efficient build - multiple threads
   @Test
   public void testEfficientBuildMultipleThreadsAddAndRemoveJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildMultipleThreadsAddAndRemoveJavaFile", true, true, true, 2, true, false);
      testAddAndRemoveJavaFile(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsAddJavaFileAndRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildMultipleThreadsAddJavaFileAndRemoveMethod", true, true, true, 2, true, false);
      testAddJavaFileAndRemoveMethod(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsAddJavaFileAndRemoveAllMethods() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildMultipleThreadsAddJavaFileAndRemoveAllMethods", true, true, true, 2, true, false);
      testAddJavaFileAndRemoveAllMethods(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildMultipleThreadsAddSomeFilesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildMultipleThreadsAddSomeFilesAndRemoveOne", true, true, true, 2, true, false);
      testAddSomeFilesAndRemoveOne(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsAddPackagesAndRemoveOne() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoDeleteTests_testEfficientBuildMultipleThreadsAddPackagesAndRemoveOne", true, true, true, 2, true, false);
      testAddPackagesAndRemoveOne(project);
      project.close(null);
   }
   
   
   
   private void testAddAndRemoveJavaFile(IProject project) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("SingleJavaFileTest.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("SingleJavaFileTest.java").append("SingleJavaFileTest[SingleJavaFileTest__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AutoDeleteTests/testAddAndRemoveJavaFile", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      javaFile.delete(IResource.FORCE, null);
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
   }
   
   
   private void testAddJavaFileAndRemoveMethod(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AutoDeleteTests/testAddJavaFileAndRemoveMethod/first", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/AutoDeleteTests/testAddjavaFileAndRemoveMethod/second/File.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
   }

   
   private void testAddJavaFileAndRemoveAllMethods(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AutoDeleteTests/testAddJavaFileAndRemoveAllMethods/first", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/AutoDeleteTests/testAddjavaFileAndRemoveAllMethods/second/File.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
   }
   
   
   private void testAddSomeFilesAndRemoveOne(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File1.java").append("File1[File1__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AutoDeleteTests/testAddSomeFilesAndRemoveOne", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      
      javaFile1.delete(IResource.FORCE, null);
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && !javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
   }   
   
   
   private void testAddPackagesAndRemoveOne(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("package0").append("File.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("package1").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("package0").append("File.java").append("package0_File[package0_File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("package1").append("File.java").append("package1_File[package1_File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFolder package0Folder = KeY4EclipseResourcesTestUtil.getFolder(
            project.getFullPath().append("proofs").append("package0"));
      IFolder package1Folder = KeY4EclipseResourcesTestUtil.getFolder(
            project.getFullPath().append("proofs").append("package1"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      assertTrue(!package0Folder.exists() && !package1Folder.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AutoDeleteTests/testAddPackagesAndRemoveOne", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(package0Folder.exists() && package1Folder.exists());
      
      javaFile1.delete(IResource.FORCE, null);
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && !javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      assertTrue(package0Folder.exists() && !package1Folder.exists());
   }   
   
 }