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

public class BuilderTests extends AbstractResourceTest {
   
   @Test
   public void testBuildDisabled() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testBuildDisabled", false, false, false, 1, false, false);
      testBuildDisabled(project);
      project.close(null);
   }
   
   
   //Full build - single thread
   @Test
   public void testFullBuildSingleThreadCleanBuild() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadCleanBuild", true, false, false, 1, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadAddSingleJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadAddSingleJavaFile", true, false, false, 1, false, false);
      testAddSingleJavaFile(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadAddMethod", true, false, false, 1, false, false);
      testAddMethod(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadAddJavaFilesInARow() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadAddJavaFilesInARow", true, false, false, 1, false, false);
      testAddJavaFilesInARow(project, false);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadChangeJavaFileTriveal", true, false, false, 1, false, false);
      testChangeJavaFileTriveal(project, false);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadProofFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadProofFileDeleted", true, false, false, 1, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadMetaFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadMetaFileDeleted", true, false, false, 1, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   
   
   //Full build - multiple threads
   @Test
   public void testFullBuildMultipleThreadsCleanBuild() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsCleanBuild", true, false, true, 2, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsAddSingleJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsAddSingleJavaFile", true, false, true, 2, false, false);
      testAddSingleJavaFile(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildMultipleThreadsAddMethod", true, false, true, 2, false, false);
      testAddMethod(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsAddJavaFilesInARow() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsAddJavaFilesInARow", true, false, true, 2, false, false);
      testAddJavaFilesInARow(project, false);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsChangeJavaFileTriveal", true, false, true, 2, false, false);
      testChangeJavaFileTriveal(project, false);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsProofFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsProofFileDeleted", true, false, true, 2, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsMetaFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsMetaFileDeleted", true, false, true, 2, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   
   
   //Efficient build - single thread
   @Test
   public void testEfficientBuildSingleThreadCleanBuild() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadCleanBuild", true, true, false, 1, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadAddSingleJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddSingleJavaFile", true, true, false, 1, false, false);
      testAddSingleJavaFile(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildSingleThreadAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddMethod", true, true, false, 1, false, false);
      testAddMethod(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadAddJavaFilesInARow() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddJavaFilesInARow", true, true, false, 1, false, false);
      testAddJavaFilesInARow(project, true);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeJavaFileTriveal", true, true, false, 1, false, false);
      testChangeJavaFileTriveal(project, true);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadProofFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadProofFileDeleted", true, true, false, 1, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadMetaFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadMetaFileDeleted", true, true, false, 1, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadMD5Changed() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadMD5Changed", true, true, false, 1, false, false);
      testEfficientBuildMD5Changed(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadTypeChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadTypeChanged", true, true, false, 1, false, false);
      testEfficientBuildTypeChanged(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadSubTypeChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadSubTypeChanged", true, true, false, 1, false, false);
      testEfficientBuildSubTypeChanged(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadSubTypeChangedNewSubType() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientSingleThreadSubTypeChangedNewSubType", true, true, false, 1, false, false);
      testEfficientBuildSubTypeChangedNewSubType(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadSuperTypeChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientSingleThreadSuperTypeChanged", true, true, false, 1, false, false);
      testEfficientBuildSuperTypeChanged(project);
      project.close(null);
   }
   
   
   //Efficient build - multiple threads
   @Test
   public void testEfficientBuildMultipleThreadsCleanBuild() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsCleanBuild", true, true, true, 2, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsAddSingleJavaFile() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddSingleJavaFile", true, true, true, 2, false, false);
      testAddSingleJavaFile(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildMultipleThreadsAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddMethod", true, true, true, 2, false, false);
      testAddMethod(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsAddJavaFilesInARow() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddJavaFilesInARow", true, true, true, 2, false, false);
      testAddJavaFilesInARow(project, true);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeJavaFileTriveal", true, true, true, 2, false, false);
      testChangeJavaFileTriveal(project, true);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsProofFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsProofFileDeleted", true, true, true, 2, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsMetaFileDeleted() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsMetaFileDeleted", true, true, true, 2, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsMD5Changed() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsMD5Changed", true, true, true, 2, false, false);
      testEfficientBuildMD5Changed(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsTypeChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsTypeChanged", true, true, true, 2, false, false);
      testEfficientBuildTypeChanged(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsSubTypeChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsSubTypeChanged", true, true, true, 2, false, false);
      testEfficientBuildSubTypeChanged(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsSubTypeChangedNewSubType() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientMultipleThreadsSubTypeChangedNewSubType", true, true, false, 1, false, false);
      testEfficientBuildSubTypeChangedNewSubType(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsSuperTypeChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientMultipleThreadsSuperTypeChanged", true, true, true, 2, false, false);
      testEfficientBuildSuperTypeChanged(project);
      project.close(null);
   }
   
   
   private void testBuildDisabled(IProject project) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("buildDisabled").append("File.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testBuildDisabled", project.getFolder("src"));

      assertTrue(javaFile.exists());
      assertTrue(!proofFolder.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(!proofFolder.exists());
   }
   
   
   private void testCleanBuild(IProject project) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("cleanBuild").append("File.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("cleanBuild").append("File.java").append("cleanBuild_File[cleanBuild_File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().addFileExtension("meta"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testCleanBuild", project.getFolder("src"));

      assertTrue(javaFile.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      long proofFolderModStamp = proofFolder.getLocalTimeStamp();
      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      KeY4EclipseResourcesTestUtil.cleanBuild(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      assertTrue(proofFolder.getLocalTimeStamp() != proofFolderModStamp);
      assertTrue(proofFile.getLocalTimeStamp() != proofFileModStamp);
      assertTrue(metaFile.getLocalTimeStamp() != metaFileModStamp);
   }
   
   
   private void testAddSingleJavaFile(IProject project) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("single").append("javaFile").append("SingleJavaFileTest.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("single").append("javaFile").append("SingleJavaFileTest.java").append("single_javaFile_SingleJavaFileTest[single_javaFile_SingleJavaFileTest__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("single").append("javaFile").append("SingleJavaFileTest.java").append("single_javaFile_SingleJavaFileTest[single_javaFile_SingleJavaFileTest__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().addFileExtension("meta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().addFileExtension("meta"));
      
      assertTrue(!proofFolder.exists());
      assertTrue(!javaFile.exists());
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testSingleJavaFile", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
   }
   
   private void testAddMethod(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("add").append("method").append("AddMethodTest.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("add").append("method").append("AddMethodTest.java").append("add_method_AddMethodTest[add_method_AddMethodTest__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("add").append("method").append("AddMethodTest.java").append("add_method_AddMethodTest[add_method_AddMethodTest__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().addFileExtension("meta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().addFileExtension("meta"));
      
      assertTrue(!javaFile.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddMethod/firstFile", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testAddMethod/changedFile/AddMethodTest.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp != metaFile0.getLocalTimeStamp());
   }
   
   
   private void testAddJavaFilesInARow(IProject project, boolean efficientBuild) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("file").append("one").append("FirstFile.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("file").append("two").append("SecondFile.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("file").append("one").append("FirstFile.java").append("file_one_FirstFile[file_one_FirstFile__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("file").append("two").append("SecondFile.java").append("file_two_SecondFile[file_two_SecondFile__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().addFileExtension("meta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().addFileExtension("meta"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddJavaFilesInARow/firstFile", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && !javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && !javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());

      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddJavaFilesInARow/secondFile", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      if(efficientBuild){
         assertTrue(proofFile0modStamp == proofFile0.getLocalTimeStamp());
         assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
      }
      else{
         assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
         assertTrue(metaFile0modStamp != metaFile0.getLocalTimeStamp());
      }
   }
   
   
   private void testChangeJavaFileTriveal(IProject project, boolean efficientBuild) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("file").append("to").append("change").append("TrivealChangeFile.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("file").append("to").append("change").append("TrivealChangeFile.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("file").append("to").append("change").append("TrivealChangeFile.java").append("file_to_change_TrivealChangeFile[file_to_change_TrivealChangeFile__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("file").append("to").append("change").append("AnotherFile.java").append("file_to_change_AnotherFile[file_to_change_AnotherFile__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().addFileExtension("meta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().addFileExtension("meta"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeFileTriveal", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      
      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      long proofFile1modStamp = proofFile1.getLocalTimeStamp();
      long metaFile1modStamp = metaFile1.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeFileTriveal/file/to/change/TrivealChangeFile.java");
      javaFile0.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp != metaFile0.getLocalTimeStamp());
      if(efficientBuild){
         assertTrue(proofFile1modStamp == proofFile1.getLocalTimeStamp());
         assertTrue(metaFile1modStamp == metaFile1.getLocalTimeStamp());
      }
      else{
         assertTrue(proofFile1modStamp != proofFile1.getLocalTimeStamp());
         assertTrue(metaFile1modStamp != metaFile1.getLocalTimeStamp());  
      }
   }
   
   
   private void testFileDeleted(IProject project, boolean proofDeleted) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().addFileExtension("meta"));
      
      assertTrue(!javaFile.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile.exists());
      assertTrue(!metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testFileDeleted/", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists());
      assertTrue(metaFile.exists());
      
      if(proofDeleted){
         proofFile.delete(IResource.FORCE, null);
         assertTrue(!proofFile.exists());
      }
      else{
         metaFile.delete(IResource.FORCE, null);
         assertTrue(!metaFile.exists());
      }
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists());
      assertTrue(metaFile.exists());
   }
   
   
   private void testEfficientBuildMD5Changed(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("MD5").append("changed").append("FileToAdd.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MD5").append("changed").append("FileToAdd.java").append("MD5_changed_FileToAdd[MD5_changed_FileToAdd__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MD5").append("changed").append("FileToAdd.java").append("MD5_changed_FileToAdd[MD5_changed_FileToAdd__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().addFileExtension("meta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().addFileExtension("meta"));
      
      assertTrue(!javaFile.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientMD5Changed/javaFile", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      
      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      long proofFile1modStamp = proofFile1.getLocalTimeStamp();
      long metaFile1modStamp = metaFile1.getLocalTimeStamp();
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientMD5Changed/proofFile");
      proofFile0.setContents(is, IResource.FORCE, null);
      is.close();
      
      assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
      
      proofFile0modStamp = proofFile0.getLocalTimeStamp();
      metaFile0modStamp = metaFile0.getLocalTimeStamp();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp != metaFile0.getLocalTimeStamp());
      assertTrue(proofFile1modStamp == proofFile1.getLocalTimeStamp());
      assertTrue(metaFile1modStamp == metaFile1.getLocalTimeStamp());
   }
   
   
   
   
   private void testEfficientBuildTypeChanged(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("type").append("changed").append("Main.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("type").append("changed").append("A.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("type").append("changed").append("Main.java").append("type_changed_Main[type_changed_Main__main(type_changed_A)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().addFileExtension("meta"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientTypeChanged", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      long proofFilemodStamp = proofFile.getLocalTimeStamp();
      long metaFilemodStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientTypeChanged/type/changed/A.java");
      javaFile1.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFilemodStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFilemodStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testEfficientBuildSubTypeChanged(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("subType").append("changed").append("Main.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("subType").append("changed").append("A.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("subType").append("changed").append("B.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("subType").append("changed").append("Main.java").append("subType_changed_Main[subType_changed_Main__main(subType_changed_A)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().addFileExtension("meta"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientSubTypeChanged", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientSubTypeChanged/subType/changed/B.java");
      javaFile2.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testEfficientBuildSubTypeChangedNewSubType(IProject project) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("newSubType").append("changed").append("Main.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("newSubType").append("changed").append("A.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("newSubType").append("changed").append("B.java"));
      IFile javaFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("newSubType").append("changed").append("C.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("newSubType").append("changed").append("Main.java").append("newSubType_changed_Main[newSubType_changed_Main__main(newSubType_changed_A)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().addFileExtension("meta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists() && !javaFile3.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientSubTypeChangedNewSubType/javaFiles", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && !javaFile3.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && !javaFile3.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientSubTypeChangedNewSubType/newSubType", project.getFolder("src/newSubType/changed"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && javaFile3.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && javaFile3.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFile.getLocalTimeStamp() != proofFileModStamp);
      assertTrue(metaFile.getLocalTimeStamp() != metaFileModStamp);
   }
   
   
   private void testEfficientBuildSuperTypeChanged(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("SuperType.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("Type.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("Type.java").append("Type[Type__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().addFileExtension("meta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientSuperTypeChanged", project.getFolder("src"));

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(!proofFolder.exists());
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testEfficientSuperTypeChanged/SuperType.java");
      javaFile0.setContents(is, IResource.FORCE, null);
      is.close();
//      javaFile0.touch(null);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      assertTrue(proofFile.getLocalTimeStamp() != proofFileModStamp);
      assertTrue(metaFile.getLocalTimeStamp() != metaFileModStamp);
   }
}