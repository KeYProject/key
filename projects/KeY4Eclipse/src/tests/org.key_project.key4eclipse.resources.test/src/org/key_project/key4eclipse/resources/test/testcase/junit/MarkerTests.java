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
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.eclipse.BundleUtil;

// TODO: Test also the line number in all tests!
public class MarkerTests extends AbstractResourceTest {
   
   //Full build - single thread
   @Test
   public void testFullBuildSingleThreadProofClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadProofClosedMarker", true, false, false, 1, false, false);
      testProofClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadProofNotClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadProofNotClosedMarker", true, false, false, 1, false, false);
      testProofNotClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadNoDuplicatedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadNoDuplicatedMarker", true, false, false, 1, false, false);
      testNoDuplicatedMarker(project);
      project.close(null);
   }

   @Test
   public void testFullBuildSingleThreadAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadAddMethod", true, false, false, 1, false, false);
      testAddMethod(project);
      project.close(null);
   }

   @Test
   public void testFullBuildSingleThreadRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRemoveMethod", true, false, false, 1, false, false);
      testRemoveMethod(project);
      project.close(null);
   }

   @Test
   public void testFullBuildSingleThreadRecursionMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarker", true, false, false, 1, false, false);
      testRecoursionMarker(project);
      project.close(null);
   }

   @Test
   public void testFullBuildSingleThreadProblemLoaderExceptionHandler() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadProblemLoaderExceptionHandler", true, false, false, 1, false, false);
      testProblemLoaderExceptionHandler(project);
      project.close(null);
   }
   
   
 //Full build - multiple threads
   @Test
   public void testFullBuildMultipleThreadsProofClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsProofClosedMarker", true, false, true, 2, false, false);
      testProofClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsProofNotClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsProofNotClosedMarker", true, false, true, 2, false, false);
      testProofNotClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsNoDuplicatedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsNoDuplicatedMarker", true, false, true, 2, false, false);
      testNoDuplicatedMarker(project);
      project.close(null);
   }

   @Test
   public void testFullBuildMultipleThreadsAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsAddMethod", true, false, true, 2, false, false);
      testAddMethod(project);
      project.close(null);
   }

   @Test
   public void testFullBuildMultipleThreadsRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRemoveMethod", true, false, true, 2, false, false);
      testRemoveMethod(project);
      project.close(null);
   }

   @Test
   public void testFullBuildMultipleThreadsRecursionMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarker", true, false, true, 2, false, false);
      testRecoursionMarker(project);
      project.close(null);
   }

   @Test
   public void testFullBuildMultipleThreadsProblemLoaderExceptionHandler() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsProblemLoaderExceptionHandler", true, false, true, 2, false, false);
      testProblemLoaderExceptionHandler(project);
      project.close(null);
   }

   
 //Efficient build - single thread
   @Test
   public void testEfficientBuildSingleThreadProofClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadProofClosedMarker", true, true, false, 1, false, false);
      testProofClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadProofNotClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadProofNotClosedMarker", true, true, false, 1, false, false);
      testProofNotClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadNoDuplicatedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadNoDuplicatedMarker", true, true, false, 1, false, false);
      testNoDuplicatedMarker(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildSingleThreadAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadAddMethod", true, true, false, 1, false, false);
      testAddMethod(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildSingleThreadRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRemoveMethod", true, true, false, 1, false, false);
      testRemoveMethod(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildSingleThreadRecursionMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarker", true, true, false, 1, false, false);
      testRecoursionMarker(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildSingleThreadProblemLoaderExceptionHandler() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadProblemLoaderExceptionHandler", true, true, false, 1, false, false);
      testProblemLoaderExceptionHandler(project);
      project.close(null);
   }
   
   
 //Full build - multiple threads
   @Test
   public void testEfficientBuildMultipleThreadsProofClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsProofClosedMarker", true, true, true, 2, false, false);
      testProofClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsProofNotClosedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsProofNotClosedMarker", true, true, true, 2, false, false);
      testProofNotClosedMarker(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsNoDuplicatedMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsNoDuplicatedMarker", true, true, true, 2, false, false);
      testNoDuplicatedMarker(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildMultipleThreadsAddMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsAddMethod", true, true, true, 2, false, false);
      testAddMethod(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildMultipleThreadsRemoveMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRemoveMethod", true, true, true, 2, false, false);
      testRemoveMethod(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarker() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarker", true, true, true, 2, false, false);
      testRecoursionMarker(project);
      project.close(null);
   }

   @Test
   public void testEfficientBuildMultipleThreadsProblemLoaderExceptionHandler() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsProblemLoaderExceptionHandler", true, true, true, 2, false, false);
      testProblemLoaderExceptionHandler(project);
      project.close(null);
   }

   
   
   private void testProofClosedMarker(IProject project) throws CoreException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("proofClosed").append("ClosedProofFile.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testProofClosed", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(markerList.size() == 1);
      assertTrue(testMarker(markerList.get(0), MarkerManager.CLOSEDMARKER_ID, 115, 118));
   }
   
   private void testProofNotClosedMarker(IProject project) throws CoreException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("proofNotClosed").append("NotClosedProofFile.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testProofNotClosed", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(markerList.size() == 1);
      assertTrue(testMarker(markerList.get(0), MarkerManager.NOTCLOSEDMARKER_ID, 115, 118));
   }
   
   private void testNoDuplicatedMarker(IProject project) throws CoreException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("noDuplicates").append("NoDuplicatesFile.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("noDuplicates").append("NoDuplicatesTooFile.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testNoDuplicatedMarker/first", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && !javaFile1.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);

      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testNoDuplicatedMarker/second", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
   }
   
   
   private void testAddMethod(IProject project) throws CoreException, IOException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("addMethod").append("File.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testAddMethod/first", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 1);
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testAddMethod/second/File.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 2);
   }
   
   
   private void testRemoveMethod(IProject project) throws CoreException, IOException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("removeMethod").append("File.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRemoveMethod/first", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 2);
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRemoveMethod/second/File.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 1);
   }
   
   
   private void testRecoursionMarker(IProject project) throws CoreException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("MultipleRecursion.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarker", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 2);
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      if(testMarker(markerList.get(0), MarkerManager.CYCLEDETECTEDMARKER_ID, 293, 294)){
         assertTrue(testMarker(markerList.get(1), MarkerManager.CYCLEDETECTEDMARKER_ID, 446, 447));
      }
      else if(testMarker(markerList.get(0), MarkerManager.CYCLEDETECTEDMARKER_ID, 446, 447)){
         assertTrue(testMarker(markerList.get(1), MarkerManager.CYCLEDETECTEDMARKER_ID, 293, 294));
      }
      else{
         fail();
      }
   }
   
   private void testProblemLoaderExceptionHandler(IProject project) throws CoreException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("ProblemLoaderExceptionFile.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testProblemLoaderExceptionHandler", project.getFolder("src"));
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 1);
      assertTrue(testMarker(KeY4EclipseResourcesTestUtil.getAllKeYMarker(project).get(0), MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID, -1, -1));

   }
   
   
   
   private boolean testMarker(IMarker marker, String type, int startChar, int endChar) throws CoreException{
      if(marker.exists()){
         if(marker.getType().equals(type)){
            int markerStartChar = (int) marker.getAttribute(IMarker.CHAR_START, -1);
            int markerEndChar = (int) marker.getAttribute(IMarker.CHAR_END, -1);
            if(markerStartChar == startChar && markerEndChar == endChar){
               return true;
            }
         }
      }
      return false;
   }
}
