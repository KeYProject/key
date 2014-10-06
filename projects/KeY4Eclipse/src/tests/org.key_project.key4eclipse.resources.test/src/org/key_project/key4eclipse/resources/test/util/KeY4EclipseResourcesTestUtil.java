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

package org.key_project.key4eclipse.resources.test.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildJob;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.marker.MarkerUtil;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

public class KeY4EclipseResourcesTestUtil {

   
   /**
    * Creates a new KeYProject that is an {@link IJavaProject} with a KeYNature.
    * @param name - the project name
    * @return the created KeYProject
    * @throws CoreException
    * @throws InterruptedException
    */
   public static IJavaProject createKeYProject(String name) throws CoreException, InterruptedException{
      IJavaProject javaProject = TestUtilsUtil.createJavaProject(name);
      IProject project = javaProject.getProject();
      IProjectDescription description = project.getDescription();
      //Add KeYNature
      String[] newNatures = ArrayUtil.add(description.getNatureIds(), KeYProjectNature.NATURE_ID);
      description.setNatureIds(newNatures);
      project.setDescription(description, null);
      assertTrue(hasNature(KeYProjectNature.NATURE_ID, javaProject.getProject()) && hasBuilder(KeYProjectBuilder.BUILDER_ID, javaProject.getProject()));
      return javaProject;
   }
   
   
   /**
    * Checks if the given {@link IProject} has the given nature.
    * @param natureId - the given nature
    * @param project - the {@link IProject} to use
    * @return true if the {@link IProject} hat the given nature. False otherwise.
    * @throws CoreException
    */
   public static boolean hasNature(String natureId, IProject project) throws CoreException{
      IProjectDescription description = project.getDescription();
      return ArrayUtil.contains(description.getNatureIds(), natureId);
   }
   
   
   /**
    * Checks if the given {@link IProject} has the given Builder.
    * @param builderId - the given builder
    * @param project - the {@link IProject} to use
    * @return true if the {@link IProject} hat the given builder. False otherwise.
    * @throws CoreException
    */
   public static boolean hasBuilder(String builderId, IProject project) throws CoreException{
      IProjectDescription description = project.getDescription();
      ICommand keyBuilder = ArrayUtil.search(description.getBuildSpec(), new IFilter<ICommand>() {
         @Override
         public boolean select(ICommand element) {
            return element.getBuilderName().equals(KeYProjectBuilder.BUILDER_ID);
         }
      });
      if(keyBuilder != null){
         return keyBuilder.getBuilderName().equals(builderId);
      }
      return false;
   }
   
   
   /**
    * Enables or disables the AutoBuild function in eclipse.
    * @param enable - true if the AutoBuild should be enabled. False otherwise
    * @return Returns the old enabled state.
    * @throws CoreException
    */
   public static boolean enableAutoBuild(boolean enable) throws CoreException{
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      IWorkspaceDescription desc = workspace.getDescription();
      boolean oldEnabled = desc.isAutoBuilding(); 
      if (oldEnabled != enable) {
         desc.setAutoBuilding(enable);
         workspace.setDescription(desc);
      }
      return oldEnabled;
   }
   
   public static boolean isAutoBuilding(){
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      IWorkspaceDescription desc = workspace.getDescription();
      return desc.isAutoBuilding(); 
   }
   
   
   /**
    * Runs an {@link IncrementalProjectBuilder}s INCREMENTAL_BUILD for the given {@link IProject} and waits for the build to finish.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void build(IProject project) throws CoreException{
      project.build(IncrementalProjectBuilder.INCREMENTAL_BUILD, null);
      waitBuild();
   }
   
   public static void waitBuild() {
      IJobManager manager = Job.getJobManager();
      // Wait for jobs and builds.
      Job[] keyJobs = manager.find(KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB);
      Job[] buildJobs = manager.find(ResourcesPlugin.FAMILY_AUTO_BUILD);
      while (!ArrayUtil.isEmpty(keyJobs) || !ArrayUtil.isEmpty(buildJobs)) {
         // Sleep some time but allow the UI to do its tasks
         if (Display.getDefault().getThread() == Thread.currentThread()) {
            int i = 0;
            while (Display.getDefault().readAndDispatch() && i < 1000) {
               i++;
            }
         }
         else {
            TestUtilsUtil.sleep(100);
         }
         // Check if jobs are still running
         keyJobs = manager.find(KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB);
         buildJobs = manager.find(ResourcesPlugin.FAMILY_AUTO_BUILD);
      }
   }
   
   public static void cleanBuild(IProject project) throws CoreException{
      project.build(IncrementalProjectBuilder.CLEAN_BUILD, null);
      waitBuild();
   }
   
   
   /**
    * Loads a given proof{@linkIFile} and returns the loaded {@link Proof}.
    * @param file - the {@link IFile} to load
    * @param project - the {@link IProject} to use
    * @return the loaded {@link Proof}
    * @throws CoreException
    * @throws ProblemLoaderException
    */
   public static Proof loadProofFile(File file, IProject project) throws CoreException, ProblemLoaderException{
      File location = ResourceUtil.getLocation(project);
      File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
      List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
      KeYEnvironment<CustomUserInterface> environment = KeYEnvironment.load(location, classPaths, bootClassPath);
      environment = KeYEnvironment.load(file, null, null);
      return environment.getLoadedProof();
   }
   
   
   /**
    * Returns the proof{@link IFolder} for the given {@link IProject}.
    * @param project - the {@link IProject} to use
    * @return the proof{@link IFolder}
    */
   public static IFolder getProofFolder(IProject project){
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath proofFolderPath = project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME);
      return root.getFolder(proofFolderPath);
   }
   
   
   /**
    * Collects all {@link IMarker} of the given type for the given {@link IResource}.
    * @param type - the type to use
    * @param res - the {@link IResource} to use
    * @return the {@link LinkedList} with the collected {@link IMarker}
    * @throws CoreException
    */
   public static LinkedList<IMarker> getKeYMarkerByType(String type, IResource res) throws CoreException{
      LinkedList<IMarker> markerList = new LinkedList<IMarker>();
      IMarker[] markers = res.findMarkers(type, true, IResource.DEPTH_INFINITE);
      for(IMarker marker : markers){
         markerList.add(marker);
      }
      return markerList;
   }
   
   
   /**
    * Collects all KeY{@link IMarker} for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @return the {@link LinkedList} with the collected {@link IMarker}
    * @throws CoreException
    */
   public static LinkedList<IMarker> getAllKeYMarker(IResource res) throws CoreException{
      LinkedList<IMarker> allMarkerList = getKeYMarkerByType(MarkerUtil.CLOSEDMARKER_ID, res);
      allMarkerList.addAll(getKeYMarkerByType(MarkerUtil.NOTCLOSEDMARKER_ID, res));
      allMarkerList.addAll(getKeYMarkerByType(MarkerUtil.RECURSIONMARKER_ID, res));
      allMarkerList.addAll(getKeYMarkerByType(MarkerUtil.PROBLEMLOADEREXCEPTIONMARKER_ID, res));
      return allMarkerList;
   }
   
   public static int getMarkerCount(IResource res) throws CoreException{
      return getAllKeYMarker(res).size();
   }
   
   
   public static void setKeYProjectProperties(IProject project, boolean buildProofs, boolean startupBuilds, boolean buildProofsEfficient, boolean enableMultiThreading, int numberOfThreads, boolean autoDeleteProofFiles) throws CoreException{
      KeYProjectProperties.setEnableKeYResourcesBuilds(project, buildProofs);
      KeYProjectProperties.setEnableBuildOnStartup(project, startupBuilds);
      KeYProjectProperties.setEnableBuildProofsEfficient(project, buildProofsEfficient);
      KeYProjectProperties.setEnableMultiThreading(project, enableMultiThreading);
      KeYProjectProperties.setNumberOfThreads(project, String.valueOf(numberOfThreads));
      KeYProjectProperties.setAutoDeleteProofFiles(project, autoDeleteProofFiles);
   }
   
   public static IProject initializeTest(String projectName, boolean buildProofs, boolean startupBuilds, boolean buildProofsEfficient, boolean enableMultiThreading, int numberOfThreads, boolean autoDeleteProofFiles) throws CoreException, InterruptedException{
      //turn off autobuild
//      enableAutoBuild(false);
      //create a KeYProject
      IJavaProject keyProject = createKeYProject(projectName);
      IProject project = keyProject.getProject();
      setKeYProjectProperties(project, buildProofs, startupBuilds, buildProofsEfficient, enableMultiThreading, numberOfThreads, autoDeleteProofFiles);
      //build
      KeY4EclipseResourcesTestUtil.build(project);
      return project;
   }
   
   public static boolean proofFolderExists(IProject project){
      IFolder proofFolder = getProofFolder(project);
      return proofFolder.exists();
   }
   
   public static boolean fileExists(IPath path){
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      return root.getFile(path).exists();
   }
   
   public static IFile getFile(IPath path){
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      return root.getFile(path);
   }
   
   public static IFolder getFolder(IPath path){
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      return root.getFolder(path);
   }

   public static void assertCleanProofFolder(IFolder proofFolder) throws CoreException {
      try {
         if (proofFolder.exists()) {
            ProofFileCountVisitor visitor = new ProofFileCountVisitor();
            proofFolder.accept(visitor, IResource.DEPTH_INFINITE, true);
            assertEquals(0, visitor.getProofFileCount());
            assertEquals(0, visitor.getMetaFileCount());
            IFile logFile = proofFolder.getFile(LogManager.LOG_FILE_NAME);
            if (logFile.exists()) {
               assertTrue(LogManager.getInstance().countRecords(logFile.getProject()) >= 1);
            }
         }
      }
      catch (IOException e) {
         throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage(), e));
      }
   }
   
   private static class ProofFileCountVisitor implements IResourceVisitor {
      private int proofFileCount = 0;
      
      private int metaFileCount = 0;

      @Override
      public boolean visit(IResource resource) throws CoreException {
         if (resource instanceof IFile) {
            if (KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(resource.getFileExtension())) {
               proofFileCount ++;
            }
            else if (KeYResourcesUtil.META_FILE_EXTENSION.equals(resource.getFileExtension())) {
               metaFileCount ++;
            }
         }
         return true;
      }

      public int getProofFileCount() {
         return proofFileCount;
      }

      public int getMetaFileCount() {
         return metaFileCount;
      }
   }
}