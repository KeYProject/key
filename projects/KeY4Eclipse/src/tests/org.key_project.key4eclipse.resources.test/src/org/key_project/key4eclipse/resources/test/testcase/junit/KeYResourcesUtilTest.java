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

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.junit.Test;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link KeYResourcesUtil}.
 * @author Martin Hentschel
 */
public class KeYResourcesUtilTest extends TestCase {
   /**
    * Tests {@link KeYResourcesUtil#isProofFolder(org.eclipse.core.resources.IFolder)}
    */
   @Test
   public void testIsProofFolder() throws CoreException, InterruptedException {
      assertFalse(KeYResourcesUtil.isProofFolder(null));
      IProject project = TestUtilsUtil.createProject("KeYResourcesUtilTest_testIsProofFolder_general");
      IFolder projectNotProof = TestUtilsUtil.createFolder(project, KeYResourcesUtil.PROOF_FOLDER_NAME + "Fake");
      IFolder projectNotProofSub = TestUtilsUtil.createFolder(projectNotProof, KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder projectProof = TestUtilsUtil.createFolder(project, KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder projectProofSub = TestUtilsUtil.createFolder(projectProof, KeYResourcesUtil.PROOF_FOLDER_NAME);
      assertFalse(KeYResourcesUtil.isProofFolder(projectNotProof));
      assertFalse(KeYResourcesUtil.isProofFolder(projectNotProofSub));
      assertFalse(KeYResourcesUtil.isProofFolder(projectProof));
      assertFalse(KeYResourcesUtil.isProofFolder(projectProofSub));
      IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeYResourcesUtilTest_testIsProofFolder_java");
      IFolder javaNotProof = TestUtilsUtil.createFolder(javaProject.getProject(), KeYResourcesUtil.PROOF_FOLDER_NAME + "Fake");
      IFolder javaNotProofSub = TestUtilsUtil.createFolder(javaNotProof, KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder javaProof = TestUtilsUtil.createFolder(javaProject.getProject(), KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder javaProofSub = TestUtilsUtil.createFolder(javaProof, KeYResourcesUtil.PROOF_FOLDER_NAME);
      assertFalse(KeYResourcesUtil.isProofFolder(javaNotProof));
      assertFalse(KeYResourcesUtil.isProofFolder(javaNotProofSub));
      assertFalse(KeYResourcesUtil.isProofFolder(javaProof));
      assertFalse(KeYResourcesUtil.isProofFolder(javaProofSub));
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYResourcesUtilTest_testIsProofFolder_key");
      IFolder keyNotProof = TestUtilsUtil.createFolder(keyProject.getProject(), KeYResourcesUtil.PROOF_FOLDER_NAME + "Fake");
      IFolder keyNotProofSub = TestUtilsUtil.createFolder(keyNotProof, KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder keyProof = TestUtilsUtil.createFolder(keyProject.getProject(), KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder keyProofSub = TestUtilsUtil.createFolder(keyProof, KeYResourcesUtil.PROOF_FOLDER_NAME);
      assertFalse(KeYResourcesUtil.isProofFolder(keyNotProof));
      assertFalse(KeYResourcesUtil.isProofFolder(keyNotProofSub));
      assertTrue(KeYResourcesUtil.isProofFolder(keyProof));
      assertFalse(KeYResourcesUtil.isProofFolder(keyProofSub));
   }
   
   /**
    * Tests {@link KeYResourcesUtil#isKeYProject(org.eclipse.core.resources.IProject)}
    */
   @Test
   public void testIsKeYProject() throws CoreException, InterruptedException {
      assertFalse(KeYResourcesUtil.isKeYProject(null));
      IProject project = TestUtilsUtil.createProject("KeYResourcesUtilTest_testIsKeYProject_general");
      assertFalse(KeYResourcesUtil.isKeYProject(project));
      IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeYResourcesUtilTest_testIsKeYProject_java");
      assertFalse(KeYResourcesUtil.isKeYProject(javaProject.getProject()));
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYResourcesUtilTest_testIsKeYProject_key");
      assertTrue(KeYResourcesUtil.isKeYProject(keyProject.getProject()));
   }
}