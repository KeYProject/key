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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.BundleUtil;

public class HideMetaFilesTests extends AbstractResourceTest {
   
   @Test
   public void testHideMetaFiles() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("HideMetaFilesTests_testHideMetaFiles", true, false, false, 1, false, false);
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("hideMetaFiles").append("HideMeta.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("hideMetaFiles").append("HideMeta.java").append("hideMetaFiles_HideMeta[hideMetaFiles_HideMeta__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("hideMetaFiles").append("HideMeta.java").append("hideMetaFiles_HideMeta[hideMetaFiles_HideMeta__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().addFileExtension("meta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().addFileExtension("meta"));
   
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/HideMetaFilesTests/testHideMetaFiles", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(!javaFile.isHidden());
      assertTrue(!proofFolder.isHidden());
      assertTrue(!proofFile0.isHidden() && !proofFile1.isHidden());
      assertTrue(!metaFile0.isHidden() && !metaFile1.isHidden());
      
      KeYProjectProperties.setHideMetaFiles(project, true);
      KeYResourcesUtil.hideMetaFiles(project);

      assertTrue(!javaFile.isHidden());
      assertTrue(!proofFolder.isHidden());
      assertTrue(!proofFile0.isHidden() && !proofFile1.isHidden());
      assertTrue(metaFile0.isHidden() && metaFile1.isHidden());

      project.close(null);
   }
   
   
   @Test
   public void testShowMetaFiles() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("HideMetaFilesTests_testShowMetaFiles", true, false, false, 1, false, true);
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("showMetaFiles").append("ShowMeta.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("showMetaFiles").append("ShowMeta.java").append("showMetaFiles_ShowMeta[showMetaFiles_ShowMeta__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("showMetaFiles").append("ShowMeta.java").append("showMetaFiles_ShowMeta[showMetaFiles_ShowMeta__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().addFileExtension("meta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().addFileExtension("meta"));
   
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/HideMetaFilesTests/testShowMetaFiles", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(!javaFile.isHidden());
      assertTrue(!proofFolder.isHidden());
      assertTrue(!proofFile0.isHidden() && !proofFile1.isHidden());
      assertTrue(metaFile0.isHidden() && metaFile1.isHidden());
   
      KeYProjectProperties.setHideMetaFiles(project, false);
      KeYResourcesUtil.hideMetaFiles(project);
   
      assertTrue(!javaFile.isHidden());
      assertTrue(!proofFolder.isHidden());
      assertTrue(!proofFile0.isHidden() && !proofFile1.isHidden());
      assertTrue(!metaFile0.isHidden() && !metaFile1.isHidden());

      project.close(null);
   }
}
