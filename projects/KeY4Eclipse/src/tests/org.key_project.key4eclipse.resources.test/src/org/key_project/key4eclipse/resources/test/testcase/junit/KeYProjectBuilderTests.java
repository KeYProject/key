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

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IJavaProject;
import org.junit.Test;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;

public class KeYProjectBuilderTests extends TestCase{
   
   /**
    * This test add a Java{@link IFile} to a KeYProject and checks if the {@link Proof}s and {@link IMarker} were created.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testJavaFileAddedProofClosed() throws CoreException, InterruptedException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileAddedProofClosed");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFiles
      IPath pathAdd = project.getFullPath().append("Proofs").append("add").append("java").append("test").append("AddJavaTest.java").append("add.java.test.AddJavaTest[add.java.test.AddJavaTest__add(int,int)].JML operation contract.0.proof");
      IPath pathSub = project.getFullPath().append("Proofs").append("add").append("java").append("test").append("AddJavaTest.java").append("add.java.test.AddJavaTest[add.java.test.AddJavaTest__sub(int,int)].JML operation contract.0.proof");
      IFile proofAdd = root.getFile(pathAdd);
      IFile proofSub = root.getFile(pathSub);
      //make sure that the expected proofFiles dont't exist yet
      assertTrue(!proofAdd.exists() && !proofSub.exists());
      //get the javaFile which will be added
      IPath javaFilePath = project.getFullPath().append("src").append("add").append("java").append("test").append("AddJavaTest.java");
      IFile javaFile = root.getFile(javaFilePath);
      //make sure that the javaFile doesn't exists yet
      assertFalse(javaFile.exists());
      //add the JavaFile
      IFolder src = project.getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddTests/testJavaFileAddedProofClosed", src);
      //make sure that the javaFile exists now
      assertTrue(javaFile.exists());
      //make sure that there are no KeYMarker on the added resource
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile).isEmpty());
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if the proof files were created
      assertTrue(proofAdd.exists() && proofSub.exists());
      //check if the marker were set
      LinkedList<IMarker> allMarkerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(allMarkerList.size() == 2);
      for(IMarker marker : allMarkerList){
         String markerType = marker.getType();
         assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      }
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);;  
   }
   
   
   /**
    * This test add a Java{@link IFile} to a KeYProject and checks if the {@link Proof}s and {@link IMarker} were created.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testJavaFileAddedProofNotClosed() throws CoreException, InterruptedException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileAddedProofNotClosed");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFiles
      IPath pathAdd = project.getFullPath().append("Proofs").append("add").append("java").append("test").append("AddJavaTest.java").append("add.java.test.AddJavaTest[add.java.test.AddJavaTest__add(int,int)].JML operation contract.0.proof");
      IPath pathSub = project.getFullPath().append("Proofs").append("add").append("java").append("test").append("AddJavaTest.java").append("add.java.test.AddJavaTest[add.java.test.AddJavaTest__sub(int,int)].JML operation contract.0.proof");
      IFile proofAdd = root.getFile(pathAdd);
      IFile proofSub = root.getFile(pathSub);
      //make sure that the expected proofFiles dont't exist yet
      assertTrue(!proofAdd.exists() && !proofSub.exists());
      //get the javaFile which will be added
      IPath javaFilePath = project.getFullPath().append("src").append("add").append("java").append("test").append("AddJavaTest.java");
      IFile javaFile = root.getFile(javaFilePath);
      //make sure that the javaFile doesn't exists yet
      assertFalse(javaFile.exists());
      //add the JavaFile
      IFolder src = project.getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddTests/testJavaFileAddedProofNotClosed", src);
      //make sure that the javaFile exists now
      assertTrue(javaFile.exists());
      //make sure that there are no KeYMarker on the added resource
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile).isEmpty());
    //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if the proof files were created
      assertTrue(proofAdd.exists() && proofSub.exists());
      //check if the marker were set
      LinkedList<IMarker> allMarkerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(allMarkerList.size() == 2);
      for(IMarker marker : allMarkerList){
         String markerType = marker.getType();
         assertTrue( markerType.equals(MarkerManager.CLOSEDMARKER_ID) 
                  || markerType.equals(MarkerManager.NOTCLOSEDMARKER_ID));
      }
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   /**
    * Adds a Java{@link IFile} which causes a {@link ProblemLoaderException} and checks if 
    * the ProblemException{@link IMarker} was set and no {@link Proof}s were created after the build.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testJavaFileAddedWithProblemLoaderException() throws CoreException, InterruptedException{
    //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileAddedWithProblemLoaderException");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFiles
      IPath pathAdd = project.getFullPath().append("Proofs").append("add").append("java").append("test").append("AddJavaTest.java").append("add.java.test.AddJavaTest[add.java.test.AddJavaTest__add(int,int)].JML operation contract.0.proof");
      IPath pathSub = project.getFullPath().append("Proofs").append("add").append("java").append("test").append("AddJavaTest.java").append("add.java.test.AddJavaTest[add.java.test.AddJavaTest__sub(int,int)].JML operation contract.0.proof");
      IFile proofAdd = root.getFile(pathAdd);
      IFile proofSub = root.getFile(pathSub);
      //make sure that the proofFiles don't exist yet
      assertTrue(!proofAdd.exists() && !proofSub.exists());
      //get the javaFile which will be added
      IPath javaFilePath = project.getFullPath().append("src").append("add").append("java").append("test").append("AddJavaTest.java");
      IFile javaFile = root.getFile(javaFilePath);
      //make sure that the javaFile doesn't exists yet
      assertFalse(javaFile.exists());
      //add the JavaFile
      IFolder src = project.getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddTests/testJavaFileAddedWithProblemLoaderException", src);
      //make sure that the javaFile exists now
      assertTrue(javaFile.exists());
      //make sure that there are no KeYMarker on the added resource
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile).isEmpty());
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if the proof files were created
      assertTrue(!proofAdd.exists() && !proofSub.exists());
      assertTrue(!proofFolder.exists());
      //check if the marker were set
      LinkedList<IMarker> allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFile);
      assertTrue(allMarker.size() == 0);
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(project);
      assertTrue(allMarker.size() == 1 && allMarker.get(0).getType().equals(MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID));
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   /**
    * This test adds a non-Java{@link IFile} to a KeYProject and checks if any {@link Proof}s were created.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testNonJavaFileAdded() throws CoreException, InterruptedException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testNonJavaFileAdded");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //add the non-JavaFiles
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddTests/testNonJavaFileAdded", project);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the ProofFolder was not created
      assertFalse(proofFolder.exists());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   /**
    * This test adds a Java{@link IFile} to a KeYProject. After the build a {@link IFile} will be added to the proof 
    *  {@link IFolder}. Then it will be checked if the added {@link IFile} was deleted and the proof{@link IFile}s still exist.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testFileAddedToProofFolder() throws CoreException, InterruptedException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testFileAddedToProofFolder");
      IProject project = keyProject.getProject();
      //enable auto proof file remove
      KeYProjectProperties.setAutoDeleteProofFiles(project, true);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFilePath = proofFolder.getFullPath().append("javaFile").append("aJavaFile.java").append("javaFile.aJavaFile[javaFile.aJavaFile__add(int,int)].JML operation contract.0.proof");
      IFile proofFile = root.getFile(proofFilePath);
      //make sure that the expected proofFile doesnt't exists yet
      assertFalse(proofFile.exists());
      //add a JavaFile
      IFolder src = project.getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddTests/testFileAddedToProofFolder/firstAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder and proofFile exists
      assertTrue(proofFolder.exists() && proofFile.exists());
      //get expected IFile and IFolder which will be added
      IFolder addedFolder = root.getFolder(proofFolder.getFullPath().append("aFolder"));
      IFile addedFile = root.getFile(addedFolder.getFullPath().append("anyFile"));
      //add a file to the proofFolder
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddTests/testFileAddedToProofFolder/secondAdd", proofFolder);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if added File and Folder were deleted
      assertFalse(addedFolder.exists() || addedFile.exists());
      //check if the proof File and Folder still exist
      assertTrue(proofFolder.exists() && proofFile.exists());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
      
   }
   
   
   /**
    * This test adds two Java{@link IFile}s with different packages to a KeYProject. Right after building 
    * the {@link Proof}s, one of the Java{@link IFile}s will be deleted. If all {@link Proof}s and all 
    * associated proof{@link IFolder}s of this Java{@link IFile} were deleted, the second Java{@link IFile} 
    * will be deleted. The test is passed if the whole Proof{@link IFolder} is deleted after that.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testJavaFileDeleted() throws CoreException, InterruptedException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileDeleted");
      IProject project = keyProject.getProject();
      //enable auto proof file remove
      KeYProjectProperties.setAutoDeleteProofFiles(project, true);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFiles
      IPath javaFileOneProofOnePath = project.getFullPath().append("Proofs").append("javaFile").append("to").append("delete").append("deletableJavaFile.java").append("javaFile.to.delete.deletableJavaFile[javaFile.to.delete.deletableJavaFile__add(int,int)].JML operation contract.0.proof");
      IPath javaFileOneProofTwoPath = project.getFullPath().append("Proofs").append("javaFile").append("to").append("delete").append("deletableJavaFile.java").append("javaFile.to.delete.deletableJavaFile[javaFile.to.delete.deletableJavaFile__sub(int,int)].JML operation contract.0.proof");
      IPath javaFileTwoProofOnePath = project.getFullPath().append("Proofs").append("javaFile").append("tooo").append("delete").append("anotherDeletableJavaFile.java").append("javaFile.tooo.delete.anotherDeletableJavaFile[javaFile.tooo.delete.anotherDeletableJavaFile__mul(int,int)].JML operation contract.0.proof");
      IFile javaFileOneProofOneFile = root.getFile(javaFileOneProofOnePath);
      IFile javaFileOneProofTwoFile = root.getFile(javaFileOneProofTwoPath);
      IFile javaFileTwoProofOneFile = root.getFile(javaFileTwoProofOnePath);
      //make sure that the expected proofFiles dont't exist yet
      assertTrue(!javaFileOneProofOneFile.exists() && !javaFileOneProofTwoFile.exists() && !javaFileTwoProofOneFile.exists());
      //get the javaFiles which will be added
      IPath javaFileOnePath = project.getFullPath().append("src").append("javaFile").append("to").append("delete").append("deletableJavaFile.java");
      IPath javaFileTwoPath = project.getFullPath().append("src").append("javaFile").append("tooo").append("delete").append("anotherDeletableJavaFile.java");
      IFile javaFileOne = root.getFile(javaFileOnePath);
      IFile javaFileTwo = root.getFile(javaFileTwoPath);
      //make sure that they don't exist yet
      assertTrue(!javaFileOne.exists() && !javaFileTwo.exists());
      //add the JavaFiles
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/DeleteTests/testJavaFileDeleted", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if the javaFiles and the expected proofFiles exist
      assertTrue(javaFileOne.exists() && javaFileTwo.exists());
      assertTrue(javaFileOneProofOneFile.exists() && javaFileOneProofTwoFile.exists() && javaFileTwoProofOneFile.exists());
      //make sure that javaFileOne has two and javaFileTwo one KeYMarker
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne).size() == 2 && KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileTwo).size() == 1);
      //delete the first JavaFile
      javaFileOne.delete(true, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if java and its proofFiles were deleted
      assertTrue(!javaFileOne.exists() && javaFileTwo.exists());
      assertTrue(!javaFileOneProofOneFile.exists() && !javaFileOneProofTwoFile.exists() && javaFileTwoProofOneFile.exists());
      //check if the right folder structure was deleted
      IFolder proofFolderOne = root.getFolder(project.getFullPath().append("Proofs").append("javaFile").append("to").append("delete").append("deletableJavaFile.java"));
      IFolder proofFolderTwo = root.getFolder(project.getFullPath().append("Proofs").append("javaFile").append("to").append("delete"));
      IFolder proofFolderThree = root.getFolder(project.getFullPath().append("Proofs").append("javaFile").append("to"));
      IFolder proofFolderFour = root.getFolder(project.getFullPath().append("Proofs").append("javaFile"));
      assertTrue(!proofFolderOne.exists() && !proofFolderTwo.exists() && !proofFolderThree.exists() && proofFolderFour.exists());
      assertFalse(javaFileOneProofOneFile.exists() || javaFileOneProofTwoFile.exists());
      //delete next javaFile
      javaFileTwo.delete(true, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder was deleted
      assertTrue(!javaFileTwo.exists() && !proofFolder.exists());
      //turn on autobild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   /**
    * This test adds two Java{@link IFile}s to a KeYProject. After the {@link Proof}s are build, first one of 
    * the proof{@link IFile}s will be deleted. If this {@link IFile} and all {@link IMarker} were recreated the whole proof{@link IFolder} will 
    * be deleted. The test is passed if all {@link Proof}s and {@link IMarker} are recreated.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testProofFileDeleted() throws CoreException, InterruptedException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testProofFileDeleted");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFiles
      IPath javaFileOneProofOnePath = project.getFullPath().append("Proofs").append("javaFile").append("to").append("delete").append("deletableJavaFile.java").append("javaFile.to.delete.deletableJavaFile[javaFile.to.delete.deletableJavaFile__add(int,int)].JML operation contract.0.proof");
      IPath javaFileOneProofTwoPath = project.getFullPath().append("Proofs").append("javaFile").append("to").append("delete").append("deletableJavaFile.java").append("javaFile.to.delete.deletableJavaFile[javaFile.to.delete.deletableJavaFile__sub(int,int)].JML operation contract.0.proof");
      IPath javaFileTwoProofOnePath = project.getFullPath().append("Proofs").append("javaFile").append("tooo").append("delete").append("anotherDeletableJavaFile.java").append("javaFile.tooo.delete.anotherDeletableJavaFile[javaFile.tooo.delete.anotherDeletableJavaFile__mul(int,int)].JML operation contract.0.proof");
      IFile javaFileOneProofOneFile = root.getFile(javaFileOneProofOnePath);
      IFile javaFileOneProofTwoFile = root.getFile(javaFileOneProofTwoPath);
      IFile javaFileTwoProofOneFile = root.getFile(javaFileTwoProofOnePath);
      //make sure that the expected proofFiles dont't exist yet
      assertTrue(!javaFileOneProofOneFile.exists() && !javaFileOneProofTwoFile.exists() && !javaFileTwoProofOneFile.exists());
      //get javaFiles which will be added
      IPath javaFileOnePath = project.getFullPath().append("src").append("javaFile").append("to").append("delete").append("deletableJavaFile.java");
      IPath javaFileTwoPath = project.getFullPath().append("src").append("javaFile").append("tooo").append("delete").append("anotherDeletableJavaFile.java");
      IFile javaFileOne = root.getFile(javaFileOnePath);
      IFile javaFileTwo = root.getFile(javaFileTwoPath);
      //make sure that the javaFiles dont't exist yet
      assertTrue(!javaFileOne.exists() && !javaFileTwo.exists());
      //add the javaFiles
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/DeleteTests/testProofFileDeleted", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure the javaFiles and their proofFiles exist
      assertTrue(javaFileOne.exists() && javaFileTwo.exists());
      assertTrue(javaFileOneProofOneFile.exists() && javaFileOneProofTwoFile.exists() && javaFileTwoProofOneFile.exists());
      //make sure that the marker for the javaFiles were created
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne).size() == 2 && KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileTwo).size() == 1);
      //deleteProofFile
      javaFileTwoProofOneFile.delete(true, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if file was recreated
      assertTrue(javaFileTwoProofOneFile.exists());
      //make sure that the number of marker in the javaFile are correct
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne).size() == 2 && KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileTwo).size() == 1);
      //delete whole proofFolder
      proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertTrue(proofFolder.exists());
      //TODO: warum kann der das folder nicht löschen? bei manueller ausführung geht es
      proofFolder.delete(true, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if files and folder were recreated
      assertTrue(proofFolder.exists());
      assertTrue(javaFileOneProofOneFile.exists() && javaFileOneProofTwoFile.exists() && javaFileTwoProofOneFile.exists());
      //make sure that the number of marker in the javaFile are correct
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne).size() == 2 && KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileTwo).size() == 1);
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   /**
    * Adds a Java{@link IFile} which causes a ProofNotClosed{@link IMarker}. Then Java{@link IFile} 
    * content will be changed. After the build the {@link Proof} should be closed and  the ProofNotClosed{@link IMarker} should change into a 
    * ProofClosed{@link IMarker}
    * @throws CoreException
    * @throws InterruptedException
    * @throws ProblemLoaderException
    * @throws IOException
    */
   @Test
   public void testJavaFileChangedMethodChanged() throws CoreException, InterruptedException, ProblemLoaderException, IOException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedMethodChanged");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFilePath = project.getFullPath().append("Proofs").append("method").append("changed").append("JavaFile.java").append("method.changed.JavaFile[method.changed.JavaFile__add(int,int)].JML operation contract.0.proof");
      IFile proofFile = root.getFile(proofFilePath);
      //make sure that the expected proofFile doesnt't exists yet
      assertFalse(proofFile.exists());
      //get javaFile that will be added
      IPath javaIFilePath = project.getFullPath().append("src").append("method").append("changed").append("JavaFile.java");
      IFile javaIFile = root.getFile(javaIFilePath);
      //make sure that the javaFile doesn't exist yet
      assertFalse(javaIFile.exists());
      //add the javaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChanged/fileToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile exists
      assertTrue(javaIFile.exists());
      //make sure that there is one marker in the javaFile and make sure that this marker is a "notClosedMarker"
      LinkedList<IMarker> allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      String markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.NOTCLOSEDMARKER_ID));
      //check if proofFile was created
      assertTrue(proofFile.exists());
      //load Proof and assert that it is not closed yet
      File file = proofFile.getLocation().toFile();
      Proof proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertFalse(proof.closed());
      //change the method
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChanged/changedJavaFile.java");
      javaIFile.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that there is still just one marker in the java file. but now its a "closedMarker"
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      //check if proof is closed now
      proofFile = root.getFile(proofFilePath);
      assertTrue(proofFile.exists());
      file = proofFile.getLocation().toFile();
      proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertTrue(proof.closed());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   /**
    * This test adds a Java{@link IFile} to the KeYProject. After building the {@link Proof} the 
    * JML-Specification of the {@link IMethod} will be changed. The next build will cause a 
    * ProblemLoaderException while loading the old proof{@link IFile}. In this case the {@link Proof} 
    * will be recreated. The {@link IMarker} should change form a "proofNotClosed{@linkIMarker}" to a "proofClosed{@link IMarker}".
    * @throws CoreException
    * @throws InterruptedException
    * @throws ProblemLoaderException
    * @throws IOException
    */
   @Test
   public void testJavaFileChangedMethodChangedCantLoadOldProof() throws CoreException, InterruptedException, ProblemLoaderException, IOException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedMethodChangedCantLoadOldProof");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFilePath = project.getFullPath().append("Proofs").append("method").append("changed").append("JavaFile.java").append("method.changed.JavaFile[method.changed.JavaFile__add(int,int)].JML operation contract.0.proof");
      IFile proofFile = root.getFile(proofFilePath);
      //make sure that the expected proofFile doesnt't exists yet
      assertFalse(proofFile.exists());
      //get javaFile that will be added
      IPath javaIFilePath = project.getFullPath().append("src").append("method").append("changed").append("JavaFile.java");
      IFile javaIFile = root.getFile(javaIFilePath);
      //make sure that the javaFile doesn't exist yet
      assertFalse(javaIFile.exists());
      //add the javaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChangedCantLoadOldProof/fileToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile exists
      assertTrue(javaIFile.exists());
      //make sure that there is one marker in the javaFile and make sure that this marker is a "notClosedMarker"
      LinkedList<IMarker> allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      String markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.NOTCLOSEDMARKER_ID));
      //check if proofFile was created
      assertTrue(proofFile.exists());
      //load Proof and assert that it is not closed yet
      File file = proofFile.getLocation().toFile();
      Proof proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertFalse(proof.closed());
      //change the method
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChangedCantLoadOldProof/changedJavaFile.java");
      javaIFile.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that there is still just one marker in the java file. but now its a "closedMarker"
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      //check if proof is closed now
      proofFile = root.getFile(proofFilePath);
      assertTrue(proofFile.exists());
      file = proofFile.getLocation().toFile();
      proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertTrue(proof.closed());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   @Test
   public void testJavaFileChangedMethodChangedTrivealWithClosedMarker() throws CoreException, InterruptedException, ProblemLoaderException, IOException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedMethodChangedTrivealWithClosedMarker");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFilePath = project.getFullPath().append("Proofs").append("method").append("changed").append("JavaFile.java").append("method.changed.JavaFile[method.changed.JavaFile__add(int,int)].JML operation contract.0.proof");
      IFile proofFile = root.getFile(proofFilePath);
      //make sure that the expected proofFile doesnt't exists yet
      assertFalse(proofFile.exists());
      //get javaFile that will be added
      IPath javaIFilePath = project.getFullPath().append("src").append("method").append("changed").append("JavaFile.java");
      IFile javaIFile = root.getFile(javaIFilePath);
      //make sure that the javaFile doesn't exist yet
      assertFalse(javaIFile.exists());
      //add the javaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChangedTrivealWithClosedMarker/fileToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile exists
      assertTrue(javaIFile.exists());
      //make sure that there is one marker in the javaFile and make sure that this marker is a "closedMarker"
      LinkedList<IMarker> allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      String markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      //check if proofFile was created
      assertTrue(proofFile.exists());
      //load Proof and assert that it is not closed
      File file = proofFile.getLocation().toFile();
      Proof proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertTrue(proof.closed());
      //change the method
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChangedTrivealWithClosedMarker/changedJavaFile.java");
      javaIFile.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that there is still just one marker in the java file and that its sill a "closedMarker"
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      //check if proof is closed now
      proofFile = root.getFile(proofFilePath);
      assertTrue(proofFile.exists());
      file = proofFile.getLocation().toFile();
      proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertTrue(proof.closed());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   @Test
   public void testJavaFileChangedMethodChangedTrivealWithNotClosedMarker() throws CoreException, InterruptedException, ProblemLoaderException, IOException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedMethodChangedTrivealWithNotClosedMarker");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFilePath = project.getFullPath().append("Proofs").append("method").append("changed").append("JavaFile.java").append("method.changed.JavaFile[method.changed.JavaFile__add(int,int)].JML operation contract.0.proof");
      IFile proofFile = root.getFile(proofFilePath);
      //make sure that the expected proofFile doesnt't exists yet
      assertFalse(proofFile.exists());
      //get javaFile that will be added
      IPath javaIFilePath = project.getFullPath().append("src").append("method").append("changed").append("JavaFile.java");
      IFile javaIFile = root.getFile(javaIFilePath);
      //make sure that the javaFile doesn't exist yet
      assertFalse(javaIFile.exists());
      //add the javaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChangedTrivealWithNotClosedMarker/fileToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile exists
      assertTrue(javaIFile.exists());
      //make sure that there is one marker in the javaFile and make sure that this marker is a "notClosedMarker"
      LinkedList<IMarker> allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      String markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.NOTCLOSEDMARKER_ID));
      //check if proofFile was created
      assertTrue(proofFile.exists());
      //load Proof and assert that it is not closed
      File file = proofFile.getLocation().toFile();
      Proof proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertFalse(proof.closed());
      //change the method
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodChangedTrivealWithNotClosedMarker/changedJavaFile.java");
      javaIFile.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that there is still just one marker in the java file and that its sill a "notClosedMarker"
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarker.size() == 1);
      markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.NOTCLOSEDMARKER_ID));
      //check if proof is closed now
      proofFile = root.getFile(proofFilePath);
      assertTrue(proofFile.exists());
      file = proofFile.getLocation().toFile();
      proof = KeY4EclipseResourcesTestUtil.loadProofFile(file, project);
      assertFalse(proof.closed());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   @Test
   public void testJavaFileChangedMethodAdded() throws CoreException, InterruptedException, IOException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedMethodAdded");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFileMethodOnePath = project.getFullPath().append("Proofs").append("method").append("added").append("JavaFile.java").append("method.added.JavaFile[method.added.JavaFile__add(int,int)].JML operation contract.0.proof");
      IPath proofFileMethodTwoPath = project.getFullPath().append("Proofs").append("method").append("added").append("JavaFile.java").append("method.added.JavaFile[method.added.JavaFile__sub(int,int)].JML operation contract.0.proof");
      IFile proofFileMethodOne = root.getFile(proofFileMethodOnePath);
      IFile proofFileMethodTwo = root.getFile(proofFileMethodTwoPath);
      //make sure that the proofFiles don't exist yet
      assertFalse(proofFileMethodOne.exists() || proofFileMethodTwo.exists());
      //get the javaFile which will be added
      IPath javaIFilePath = project.getFullPath().append("src").append("method").append("added").append("JavaFile.java");
      IFile javaIFile = root.getFile(javaIFilePath);
      //make sure that the file doesn't exist yet
      assertFalse(javaIFile.exists());
      //add the javaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodAdded/fileToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the java file exists now
      assertTrue(javaIFile.exists());
      //make sure that the marker were set correct
      LinkedList<IMarker> allMarkerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarkerList.size() == 1);
      String markerType = allMarkerList.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      //check if proofFileOne was created and second file is missing
      assertTrue(proofFileMethodOne.exists() && !proofFileMethodTwo.exists());
      //change the method
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedMethodAdded/changedJavaFile.java");
      javaIFile.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if both proofFile were created
      assertTrue(proofFileMethodOne.exists() && proofFileMethodTwo.exists());
      //make sure that the marker were set correct
      allMarkerList = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile);
      assertTrue(allMarkerList.size() == 2);
      for(IMarker marker : allMarkerList){
         markerType = marker.getType();
         assertTrue( markerType.equals(MarkerManager.CLOSEDMARKER_ID) 
                  || markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      }
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   @Test
   public void testJavaFileChangedSingleMethodRemoved() throws CoreException, InterruptedException, IOException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedSingleMethodRemoved");
      IProject project = keyProject.getProject();
      //enable auto proof file remove
      KeYProjectProperties.setAutoDeleteProofFiles(project, true);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFiles
      IPath proofFileMethodOnePath = project.getFullPath().append("Proofs").append("method").append("removed").append("JavaFile.java").append("method.removed.JavaFile[method.removed.JavaFile__add(int,int)].JML operation contract.0.proof");
      IPath proofFileMethodTwoPath = project.getFullPath().append("Proofs").append("method").append("removed").append("JavaFile.java").append("method.removed.JavaFile[method.removed.JavaFile__sub(int,int)].JML operation contract.0.proof");
      IPath proofFileMethodThreePath = project.getFullPath().append("Proofs").append("method").append("removed").append("JavaFile.java").append("method.removed.JavaFile[method.removed.JavaFile__mul(int,int)].JML operation contract.0.proof");
      IFile proofFileMethodOne = root.getFile(proofFileMethodOnePath);
      IFile proofFileMethodTwo = root.getFile(proofFileMethodTwoPath);
      IFile proofFileMethodThree = root.getFile(proofFileMethodThreePath);
      //make sure that the proofFiles don't exist yet
      assertFalse(proofFileMethodOne.exists() || proofFileMethodTwo.exists() || proofFileMethodThree.exists());
      //get the javaFiles which will be added
      IPath javaIFilePath = project.getFullPath().append("src").append("method").append("removed").append("JavaFile.java");
      IFile javaIFile = root.getFile(javaIFilePath);
      //make sure that the javaFile doesn't exists yet
      assertFalse(javaIFile.exists());
      //add the javaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedSingleMethodRemoved/fileToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile exists now
      assertTrue(javaIFile.exists());
      //check the number of marker
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile).size() == 3);
      //check if all proofFile were created
      assertTrue(proofFileMethodOne.exists() && proofFileMethodTwo.exists() && proofFileMethodThree.exists());
      //remove a method
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedSingleMethodRemoved/changedJavaFile.java");
      javaIFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile still exists
      assertTrue(javaIFile.exists());
      //check the number of marker
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile).size() == 2);
      //check if the proofFile was removed
      assertTrue(proofFileMethodOne.exists() && !proofFileMethodTwo.exists() && proofFileMethodThree.exists());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   @Test
   public void testJavaFileChangedAllMethodsRemoved() throws CoreException, InterruptedException, IOException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedAllMethodsRemoved");
      IProject project = keyProject.getProject();
      //enable auto proof file remove
      KeYProjectProperties.setAutoDeleteProofFiles(project, true);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFiles
      IPath proofFileMethodOnePath = project.getFullPath().append("Proofs").append("method").append("removed").append("JavaFile.java").append("method.removed.JavaFile[method.removed.JavaFile__add(int,int)].JML operation contract.0.proof");
      IPath proofFileMethodTwoPath = project.getFullPath().append("Proofs").append("method").append("removed").append("JavaFile.java").append("method.removed.JavaFile[method.removed.JavaFile__sub(int,int)].JML operation contract.0.proof");
      IPath proofFileMethodThreePath = project.getFullPath().append("Proofs").append("method").append("removed").append("JavaFile.java").append("method.removed.JavaFile[method.removed.JavaFile__mul(int,int)].JML operation contract.0.proof");
      IFile proofFileMethodOne = root.getFile(proofFileMethodOnePath);
      IFile proofFileMethodTwo = root.getFile(proofFileMethodTwoPath);
      IFile proofFileMethodThree = root.getFile(proofFileMethodThreePath);
      //make sure that the proofFiles don't exist yet
      assertFalse(proofFileMethodOne.exists() || proofFileMethodTwo.exists() || proofFileMethodThree.exists());
      //get the javaFiles which will be added
      IPath javaIFilePath = project.getFullPath().append("src").append("method").append("removed").append("JavaFile.java");
      IFile javaIFile = root.getFile(javaIFilePath);
      //make sure that the javaFile doesn't exists yet
      assertFalse(javaIFile.exists());
      //add the javaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedAllMethodsRemoved/fileToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile exists now
      assertTrue(javaIFile.exists());
      //check the number of marker
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile).size() == 3);
      //check if all proofFile were created
      assertTrue(proofFileMethodOne.exists() && proofFileMethodTwo.exists() && proofFileMethodThree.exists());
      //remove all methods
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedAllMethodsRemoved/changedJavaFile.java");
      javaIFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFile still exists
      assertTrue(javaIFile.exists());
      //check the number of marker
      assertTrue(KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaIFile).isEmpty());
      //check if the proofFile was removed
      assertTrue(!proofFileMethodOne.exists() && !proofFileMethodTwo.exists() && !proofFileMethodThree.exists());
      assertTrue(!proofFolder.exists());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   @Test
   public void testJavaFileChangedWithProblemLoaderException() throws CoreException, IOException, InterruptedException{
    //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testJavaFileChangedWithProblemLoaderException");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFileOnePath = project.getFullPath().append("Proofs").append("method").append("changed").append("JavaFile.java").append("method.changed.JavaFile[method.changed.JavaFile__add(int,int)].JML operation contract.0.proof");
      IPath proofFileTwoPath = project.getFullPath().append("Proofs").append("method").append("changed").append("anotherJavaFile.java").append("method.changed.anotherJavaFile[method.changed.anotherJavaFile__sub(int,int)].JML operation contract.0.proof");
      IFile proofFileOne = root.getFile(proofFileOnePath);
      IFile proofFileTwo = root.getFile(proofFileTwoPath);
      //make sure that the expected proofFile doesnt't exists yet
      assertTrue(!proofFileOne.exists() && !proofFileTwo.exists());
      //get javaFile that will be added
      IPath javaIFileOnePath = project.getFullPath().append("src").append("method").append("changed").append("JavaFile.java");
      IPath javaIFileTwoPath = project.getFullPath().append("src").append("method").append("changed").append("anotherJavaFile.java");
      IFile javaFileOne = root.getFile(javaIFileOnePath);
      IFile javaFileTwo = root.getFile(javaIFileTwoPath);
      //make sure that the javaFiles don't exist yet
      assertTrue(!javaFileOne.exists() && !javaFileTwo.exists());
      //add the javaFiles
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedWithProblemLoaderException/filesToAdd", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the javaFiles exist
      assertTrue(javaFileOne.exists() && javaFileTwo.exists());
      //check if proofFiles were created
      assertTrue(proofFileOne.exists() && proofFileTwo.exists());
      //make sure that there is one marker in each javaFile and make sure that this marker is a "closedMarker"
      LinkedList<IMarker> allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne);
      assertTrue(allMarker.size() == 1);
      String markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      //check the second file
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileTwo);
      assertTrue(allMarker.size() == 1);
      markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      //change the first file
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedWithProblemLoaderException/firstChangedJavaFile.java");
      javaFileOne.setContents(is, IResource.FORCE, null);
      is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedWithProblemLoaderException/resetSecondFile.java");
      javaFileTwo.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that there are no marker in the javaFiles but now its a "ProblemLoaderExceptionMarker" at the project.
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne);
      assertTrue(allMarker.size() == 0);
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne);
      assertTrue(allMarker.size() == 0);
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(project);
      assertTrue(allMarker.size() == 1 && allMarker.get(0).getType().equals(MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID));
      //change the second file
      is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedWithProblemLoaderException/firstChangedJavaFile.java");
      javaFileTwo.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the marker are still the same.
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne);
      assertTrue(allMarker.size() == 0);
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne);
      assertTrue(allMarker.size() == 0);
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(project);
      assertTrue(allMarker.size() == 1 && allMarker.get(0).getType().equals(MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID));
      
      //check if the proofFiles are still exist
      assertTrue(proofFileOne.exists() && proofFileTwo.exists());
      assertTrue(proofFolder.exists());
      //reset both files to their startvalues
      is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedWithProblemLoaderException/resetFirstFile.java");
      javaFileOne.setContents(is, IResource.FORCE, null);
      is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/ChangeTests/testJavaFileChangedWithProblemLoaderException/resetSecondFile.java");
      javaFileTwo.setContents(is, IResource.FORCE, null);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //make sure that the proofs were recreated
      assertTrue(proofFileOne.exists() && proofFileTwo.exists());
      //make sure that the marker were reseted
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileOne);
      assertTrue(allMarker.size() == 1);
      markerType = allMarker.get(0).getType();
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(javaFileTwo);
      assertTrue(allMarker.size() == 1);
      markerType = allMarker.get(0).getType(); 
      assertTrue(markerType.equals(MarkerManager.CLOSEDMARKER_ID));
      allMarker = KeY4EclipseResourcesTestUtil.getAllKeYMarker(project);
      LinkedList<IMarker> allProblemLoaderExceptionMarker = KeY4EclipseResourcesTestUtil.getKeYMarkerByType(MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID, project);
      assertTrue(allMarker.size() == 2 && allProblemLoaderExceptionMarker.size() == 0);
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
   
   
   
   /**
    * This test adds a Java{@link IFile} to a KeYProject and builds the {@link Proof}s. Then the 
    * proof{@link IFolder} will be deleted and the {@link IncrementalProjectBuilder}s CLEAN_BUILD
    * will be started. The test if passed if the proof{@link IFolder} and all {@link Proof}s exist 
    * after the build.
    * @throws CoreException
    * @throws InterruptedException
    */
   @Test
   public void testClean() throws CoreException, InterruptedException{
      //turn off autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = KeY4EclipseResourcesTestUtil.createKeYProject("KeYProjectBuilderTests_testClean");
      IProject project = keyProject.getProject();
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFolder exists
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertFalse(proofFolder.exists());
      //get expected proofFile
      IPath proofFilePath = project.getFullPath().append("Proofs").append("clean").append("test").append("CleanTest.java").append("clean.test.CleanTest[clean.test.CleanTest__add(int,int)].JML operation contract.0.proof");
      IFile proofFile = root.getFile(proofFilePath);
      assertFalse(proofFile.exists());
      //add a JavaFile
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/CleanTest/testClean", src);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      //check if proofFile was created
      assertTrue(proofFile.exists());
      //delete proofFolder
      proofFolder.delete(true, null);
      assertTrue(!proofFolder.exists() && !proofFile.exists());
      //run clean
      project.build(IncrementalProjectBuilder.CLEAN_BUILD, null);
      TestUtilsUtil.waitForBuild();
      //make sure that the proofFile and Folder were recreated
      assertTrue(proofFolder.exists() && proofFile.exists());
      //turn on autobuild
      KeY4EclipseResourcesTestUtil.enableAutoBuild(true);
   }
}