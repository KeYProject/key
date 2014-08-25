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
import org.eclipse.core.resources.ResourceAttributes;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.eclipse.BundleUtil;

public class ProofMetaFileContentExceptionTests extends AbstractResourceTest {
   
   
   @Test
   public void testInvalidXMLFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProofMetaFileContentExceptionTests_testInvalidXMLFile", true, true, false, 1, false, false);
      testEditMetaFile(project, "data/ProofMetaFileContentExceptionTests/testInvalidXMLFile/File");
      project.close(null);
   }
   
   
   @Test
   public void testNoMD5InMetaFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProofMetaFileContentExceptionTests_testNoMD5InMetaFile", true, true, false, 1, false, false);
      testEditMetaFile(project, "data/ProofMetaFileContentExceptionTests/testNoMD5InMetaFile/File");
      project.close(null);
   }
   
   
   @Test
   public void testMoreThenOneMD5InMetaFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProofMetaFileContentExceptionTests_testMoreThenOneMD5InMetaFile", true, true, false, 1, false, false);
      testEditMetaFile(project, "data/ProofMetaFileContentExceptionTests/testMoreThenOneMD5InMetaFile/File");
      project.close(null);
   }
   
   @Test
   public void testNotATypeNodeInMetaFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProofMetaFileContentExceptionTests_testNotATypeNodeInMetaFile", true, true, false, 1, false, false);
      testEditMetaFile(project, "data/ProofMetaFileContentExceptionTests/testNotATypeNodeInMetaFile/File");
      project.close(null);
   }
   
   
   @Test
   public void testNotASubTypeNodeInMetaFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProofMetaFileContentExceptionTests_testNotASubTypeNodeInMetaFile", true, true, false, 1, false, false);
      testEditMetaFile(project, "data/ProofMetaFileContentExceptionTests/testNotASubTypeNodeInMetaFile/File");
      project.close(null);
   }
   
   
   private void testEditMetaFile(IProject project, String newContentPathInBundle) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertNoProofFiles(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ProofMetaFileContentExceptionTests/testEditMetaFile/", project.getFolder("src"));

      assertTrue(javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertNoProofFiles(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      metaFile.refreshLocal(IResource.DEPTH_ZERO, null);
      ResourceAttributes resAttr = metaFile.getResourceAttributes();
      resAttr.setReadOnly(false);
      metaFile.setResourceAttributes(resAttr);
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, newContentPathInBundle);
      metaFile.setContents(is, IResource.FORCE, null);
      is.close();
      
      metaFile.refreshLocal(IResource.DEPTH_ZERO, null);
      resAttr = metaFile.getResourceAttributes();
      resAttr.setReadOnly(true);
      metaFile.setResourceAttributes(resAttr);
      
      assertTrue(metaFile.getLocalTimeStamp() != metaFileModStamp);
      metaFileModStamp = metaFile.getLocalTimeStamp();
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      assertTrue(proofFile.getLocalTimeStamp() != proofFileModStamp);
      assertTrue(metaFile.getLocalTimeStamp() != metaFileModStamp);
   }
}