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
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

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
   public void testFullBuildSingleThreadRecursionMarkerChangeOtherFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerChangeOtherFile", true, false, false, 1, false, false);
      testRecursionMarkerChangeOtherFile(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadRecursionMarkerRemoveCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerRemoveCycle", true, false, false, 1, false, false);
      testRecursionMarkerRemoveCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadRecursionMarkerChangeCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerChangeCycle", true, false, false, 1, false, false);
      testRecursionMarkerChangeCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadRecursionMarkerMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerMultipleFilesCycle", true, false, false, 1, false, false);
      testRecursionMarkerMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadRecursionMarkerRemoveMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerRemoveMultipleFilesCycle", true, false, false, 1, false, false);
      testRecursionMarkerRemoveMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadRecursionMarkerChangeMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerChangeMultipleFilesCycle", true, false, false, 1, false, false);
      testRecursionMarkerChangeMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadRecursionMarkerExpandMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerExpandMultipleFilesCycle", true, false, false, 1, false, false);
      testRecursionMarkerExpandMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildSingleThreadRecursionMarkerMultipleFilesDoubleCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildSingleThreadRecursionMarkerMultipleFilesDoubleCycle", true, false, false, 1, false, false);
      testRecursionMarkerMultipleFilesDoubleCycle(project);
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
   public void testFullBuildMultipleThreadsRecursionMarkerChangeOtherFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerChangeOtherFile", true, false, true, 2, false, false);
      testRecursionMarkerChangeOtherFile(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsRecursionMarkerRemoveCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerRemoveCycle", true, false, true, 2, false, false);
      testRecursionMarkerRemoveCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsRecursionMarkerChangeCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerChangeCycle", true, false, true, 2, false, false);
      testRecursionMarkerChangeCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsRecursionMarkerMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerMultipleFilesCycle", true, false, true, 2, false, false);
      testRecursionMarkerMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsRecursionMarkerRemoveMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerRemoveMultipleFilesCycle", true, false, true, 2, false, false);
      testRecursionMarkerRemoveMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsRecursionMarkerChangeMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerChangeMultipleFilesCycle", true, false, true, 2, false, false);
      testRecursionMarkerChangeMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsRecursionMarkerExpandMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerExpandMultipleFilesCycle", true, false, true, 2, false, false);
      testRecursionMarkerExpandMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testFullBuildMultipleThreadsRecursionMarkerMultipleFilesDoubleCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testFullBuildMultipleThreadsRecursionMarkerMultipleFilesDoubleCycle", true, false, true, 2, false, false);
      testRecursionMarkerMultipleFilesDoubleCycle(project);
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
   public void testEfficientBuildSingleThreadRecursionMarkerChangeOtherFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerChangeOtherFile()", true, true, false, 1, false, false);
      testRecursionMarkerChangeOtherFile(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadRecursionMarkerRemoveCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerRemoveCycle", true, true, false, 1, false, false);
      testRecursionMarkerRemoveCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadRecursionMarkerChangeCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerChangeCycle", true, true, false, 1, false, false);
      testRecursionMarkerChangeCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadRecursionMarkerMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerMultipleFilesCycle", true, true, false, 1, false, false);
      testRecursionMarkerMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadRecursionMarkerRemoveMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerRemoveMultipleFilesCycle", true, true, false, 1, false, false);
      testRecursionMarkerRemoveMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadRecursionMarkerChangeMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerChangeMultipleFilesCycle", true, true, false, 1, false, false);
      testRecursionMarkerChangeMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadRecursionMarkerExpandMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerExpandMultipleFilesCycle", true, true, false, 1, false, false);
      testRecursionMarkerExpandMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildSingleThreadRecursionMarkerMultipleFilesDoubleCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildSingleThreadRecursionMarkerMultipleFilesDoubleCycle", true, true, false, 1, false, false);
      testRecursionMarkerMultipleFilesDoubleCycle(project);
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
   public void testEfficientBuildMultipleThreadsRecursionMarkerChangeOtherFile() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerChangeOtherFile()", true, true, true, 2, false, false);
      testRecursionMarkerChangeOtherFile(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarkerRemoveCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerRemoveCycle", true, true, true, 2, false, false);
      testRecursionMarkerRemoveCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarkerChangeCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerChangeCycle", true, true, true, 2, false, false);
      testRecursionMarkerChangeCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarkerMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerMultipleFilesCycle", true, true, true, 2, false, false);
      testRecursionMarkerMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarkerRemoveMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerRemoveMultipleFilesCycle", true, true, true, 2, false, false);
      testRecursionMarkerRemoveMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarkerChangeMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerChangeMultipleFilesCycle", true, true, true, 2, false, false);
      testRecursionMarkerChangeMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarkerExpandMultipleFilesCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerExpandMultipleFilesCycle", true, true, true, 2, false, false);
      testRecursionMarkerExpandMultipleFilesCycle(project);
      project.close(null);
   }
   
   @Test
   public void testEfficientBuildMultipleThreadsRecursionMarkerMultipleFilesDoubleCycle() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("MarkerTests_testEfficientBuildMultipleThreadsRecursionMarkerMultipleFilesDoubleCycle", true, true, true, 2, false, false);
      testRecursionMarkerMultipleFilesDoubleCycle(project);
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
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testProofClosed", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(markerList.size() == 1);
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 115, 118));
   }
   
   private void testProofNotClosedMarker(IProject project) throws CoreException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("proofNotClosed").append("NotClosedProofFile.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testProofNotClosed", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(markerList.size() == 1);
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 121, 124));
   }
   
   private void testNoDuplicatedMarker(IProject project) throws CoreException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("noDuplicates").append("NoDuplicatesFile.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("noDuplicates").append("NoDuplicatesTooFile.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testNoDuplicatedMarker/first", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && !javaFile1.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);

      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testNoDuplicatedMarker/second", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
   }
   
   
   private void testAddMethod(IProject project) throws CoreException, IOException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("addMethod").append("File.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testAddMethod/first", project.getFolder("src"), true);
      
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
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRemoveMethod/first", project.getFolder("src"), true);
      
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
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarker", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 2);
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 285, 286));
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 410, 411));
      
   }
   
   
   private void testRecursionMarkerChangeOtherFile(IProject project) throws CoreException, IOException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("IntegerUtil.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("MultipleRecursion.java"));
      IFile tmpProofFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MultipleRecursion.java").append("0.proof"));
      IFile tmpProofFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MultipleRecursion.java").append("1.proof"));
      IFile tmpMetaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MultipleRecursion.java").append("0.proofmeta"));
      IFile tmpMetaFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MultipleRecursion.java").append("1.proofmeta"));
      
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("IntegerUtil.java").append("IntegerUtil[IntegerUtil__add(int,int)]_JML_normal_behavior_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("IntegerUtil.java").append("IntegerUtil[IntegerUtil__sub(int,int)]_JML_normal_behavior_operation_contract_0.proof"));
      IFile proofFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MultipleRecursion.java").append("MultipleRecursion[MultipleRecursion__a()]_JML_normal_behavior_operation_contract_0.proof"));
      IFile proofFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("MultipleRecursion.java").append("MultipleRecursion[MultipleRecursion__b()]_JML_normal_behavior_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile2 = KeY4EclipseResourcesTestUtil.getFile(proofFile2.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile3 = KeY4EclipseResourcesTestUtil.getFile(proofFile3.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeOtherFile/src", project.getFolder("src"), true);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeOtherFile/proofs", project.getFolder("proofs"), true);
      
      createNewFile(proofFile2, tmpProofFile2);
      createNewFile(proofFile3, tmpProofFile3);
      createNewFile(metaFile2, tmpMetaFile2);
      createNewFile(metaFile3, tmpMetaFile3);

      KeY4EclipseResourcesTestUtil.build(project);
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFile0.exists() && proofFile1.exists() && proofFile2.exists() && proofFile3.exists());
      assertTrue(metaFile0.exists() && metaFile1.exists() && metaFile2.exists() && metaFile3.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 4);
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 138, 141));
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 341, 344));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 95, 96));
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 183, 184));
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeOtherFile/src/IntegerUtil.java");
      javaFile0.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 4);
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 138, 141));
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 341, 344));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 95, 96));
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 183, 184));
   }
   
   
   private void testRecursionMarkerRemoveCycle(IProject project) throws CoreException, IOException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("MultipleRecursion.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerRemoveCycle/src", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 2);
      
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 285, 286));
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 410, 411));
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerRemoveCycle/removedCycle/MultipleRecursion.java");
      javaFile.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 2);
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 285, 286));
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 389, 390));
   }
   

   private void testRecursionMarkerChangeCycle(IProject project) throws CoreException, IOException{ //Fails because of the Bug that worng contracts are used while loading a proof.
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("MultipleRecursion.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeCycle/src", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 3);
      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 285, 286));
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 410, 411));
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 535, 536));
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeCycle/newCycle/MultipleRecursion.java");
      javaFile.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile) == 3);
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 285, 286));
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 410, 411));
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 535, 536));
   }

   private void testRecursionMarkerMultipleFilesCycle(IProject project) throws CoreException, IOException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("A.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("B.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("C.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerMultipleFilesCycle/", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 3);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile2) == 1);

      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
   }
   
   private void testRecursionMarkerRemoveMultipleFilesCycle(IProject project) throws CoreException, IOException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("A.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("B.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerRemoveMultipleFilesCycle/src/", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);

      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerRemoveMultipleFilesCycle/removedCycle/A.java");
      javaFile0.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 151, 152));
   }

   private void testRecursionMarkerChangeMultipleFilesCycle(IProject project) throws CoreException, IOException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("A.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("B.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("C.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeMultipleFilesCycle/src/", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 3);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile2) == 1);

      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeMultipleFilesCycle/changedCycle0/A.java");
      javaFile0.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerChangeMultipleFilesCycle/changedCycle1/B.java");
      javaFile1.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 151, 152));
   }
   
   private void testRecursionMarkerExpandMultipleFilesCycle(IProject project) throws CoreException, IOException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("A.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("B.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("C.java"));
      IFile javaFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("D.java"));
      IFile javaFile4 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("E.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerExpandMultipleFilesCycle/src/", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && javaFile3.exists() && javaFile4.exists());

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 5);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile2) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile3) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile4) == 1);

      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile3);
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 151, 152));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile4);
      assertTrue(testMarker(markerList, MarkerManager.NOTCLOSEDMARKER_ID, 151, 152));
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerExpandMultipleFilesCycle/expandedCycle/C.java");
      javaFile2.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 5);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile2) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile3) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile4) == 1);

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile3);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile4);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 151, 152));
   }
   
   private void testRecursionMarkerMultipleFilesDoubleCycle(IProject project) throws CoreException, IOException{
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("A.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("B.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("C.java"));
      IFile javaFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("D.java"));
      IFile javaFile4 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("recursion").append("E.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerMultipleFilesDoubleCycle/src/", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && javaFile3.exists() && javaFile4.exists());

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 5);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile2) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile3) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile4) == 1);

      LinkedList<IMarker> markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile3);
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 114, 115));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile4);
      assertTrue(testMarker(markerList, MarkerManager.CLOSEDMARKER_ID, 114, 115));
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/MarkerTests/testRecursionMarkerMultipleFilesDoubleCycle/doubleCycle/C.java");
      javaFile2.setContents(IOUtil.unifyLineBreaks(is), IResource.FORCE, null);
      is.close();
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 6);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile0) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile1) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile2) == 2);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile3) == 1);
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(javaFile4) == 1);

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile0);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile1);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115));
      
      String markerMsg0 = "Cycle detected:"+
                           StringUtil.NEW_LINE +
                           "recursion.C[recursion.C::c()].JML normal_behavior operation contract.0" +
                           StringUtil.NEW_LINE + 
                           "recursion.A[recursion.A::a()].JML normal_behavior operation contract.0" + 
                           StringUtil.NEW_LINE + 
                           "recursion.B[recursion.B::b()].JML normal_behavior operation contract.0";
      String markerMsg1 = "Cycle detected:"+
                           StringUtil.NEW_LINE +
                           "recursion.C[recursion.C::c()].JML normal_behavior operation contract.0" +
                           StringUtil.NEW_LINE + 
                           "recursion.D[recursion.D::d()].JML normal_behavior operation contract.0" + 
                           StringUtil.NEW_LINE + 
                           "recursion.E[recursion.E::e()].JML normal_behavior operation contract.0";

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115, markerMsg0));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile2);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115, markerMsg1));
      
      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile3);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115));

      markerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile4);
      assertTrue(testMarker(markerList, MarkerManager.RECURSIONMARKER_ID, 114, 115));
   }
   
   
   private void testProblemLoaderExceptionHandler(IProject project) throws CoreException{
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("ProblemLoaderExceptionFile.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MarkerTests/testProblemLoaderExceptionHandler", project.getFolder("src"), true);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(KeY4EclipseResourcesTestUtil.getMarkerCount(project) == 1);
      assertTrue(testMarker(KeY4EclipseResourcesTestUtil.getAllKeYMarker(project), MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID, -1, -1));

   }
   
   
   private boolean testMarker(LinkedList<IMarker> markerList, String type, int startChar, int endChar) throws CoreException{
      return testMarker(markerList, type, startChar, endChar, null);
   }
      
   private boolean testMarker(LinkedList<IMarker> markerList, String type, int startChar, int endChar, String message) throws CoreException{
      for(IMarker marker : markerList){
         if(marker != null && marker.exists()){
            if(marker.getType().equals(type)){
               int markerStartChar = (int) marker.getAttribute(IMarker.CHAR_START, -1);
               int markerEndChar = (int) marker.getAttribute(IMarker.CHAR_END, -1);
               if(markerStartChar == startChar && markerEndChar == endChar){
                  if(message == null){
                     return true;
                  }
                  else{
                     String msg = marker.getAttribute(IMarker.MESSAGE, "");
                     if(message.equals(msg)){
                        return true;
                     }
                  }
               }
            }
         }
      }
      return false;
   }
   
   private void createNewFile(IFile newFile, IFile oldFile) throws CoreException, IOException{
      InputStream is = oldFile.getContents();
      if(!newFile.exists()){
         newFile.create(is, IResource.FORCE, null);
      }
      else{
         newFile.setContents(is, IResource.FORCE, null);
      }
      is.close();
      oldFile.delete(IResource.FORCE, null);
   }
}