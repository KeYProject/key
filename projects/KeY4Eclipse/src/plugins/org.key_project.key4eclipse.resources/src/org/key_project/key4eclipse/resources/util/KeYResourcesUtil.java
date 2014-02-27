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

package org.key_project.key4eclipse.resources.util;

import java.util.LinkedList;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;

/**
 * @author Stefan Käsdorf
 */
public class KeYResourcesUtil {
   
   public static final String PROOF_FOLDER_NAME = "proofs";
   public static final String PROOF_FILE_EXTENSION = "proof";
   public static final String META_FILE_EXTENSION = "meta";
   
   /**
    * Runs an {@link IncrementalProjectBuilder}s INCREMENTAL_BUILD for the given {@link IProject} and waits for the build to finish.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void cleanBuildProject(final IProject project) throws CoreException{
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      IWorkspaceDescription desc = workspace.getDescription();
      boolean autoBuilding = desc.isAutoBuilding();
      if(autoBuilding){
         try {
            desc.setAutoBuilding(false);
            workspace.setDescription(desc);
            //build
            project.build(IncrementalProjectBuilder.CLEAN_BUILD, new NullProgressMonitor());
         }
         finally {
            desc.setAutoBuilding(autoBuilding);
            workspace.setDescription(desc);
         }
      }
      else{
         //build
         new Job("Converting into KeY project") {

            @Override
            protected IStatus run(IProgressMonitor monitor) {
               try {
                  project.build(IncrementalProjectBuilder.CLEAN_BUILD, monitor);
                  return Status.OK_STATUS;
               }
               catch (CoreException e) {
                  return LogUtil.getLogger().createErrorStatus(e);
               }
            }
            
         }.schedule();
      }
   }


   /**
    * Collects all meta{@link IFile}s in the given {@link IFolder} and all subfolders.
    * @param folder - the {@link IFolder} to use
    * @return a {@link LinkedList} with all meta{@link IFile}s
    * @throws CoreException
    */
   private static LinkedList<IFile> collectAllMetaFiles(IFolder folder) throws CoreException{
      MetaFileVisitor mfv = new MetaFileVisitor();
      folder.accept(mfv, IResource.DEPTH_INFINITE, IContainer.INCLUDE_HIDDEN);
      return mfv.getMetaFileList();
   }
   
   
   /**
    * Checks if the given {@link KeYJavaType} is part of the project or an external resource.
    * @param kjt - the {@link KeYJavaType} to use
    * @return false if the {@link KeYJavaType} is an internal resource
    */
   public static boolean filterKeYJavaType(KeYJavaType kjt){
      if (!(kjt.getJavaType() instanceof ClassDeclaration || 
            kjt.getJavaType() instanceof InterfaceDeclaration) || 
            KeYTypeUtil.isLibraryClass(kjt)) {
         return true;
      }
      return false;
   }
   
   
   /**
    * Applies the {@link KeYProjectProperties#PROP_HIDE_META_FILES} to all metaFiles in the given {@link IProject}.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void hideMetaFiles(IProject project) throws CoreException{
      boolean hide = KeYProjectProperties.isHideMetaFiles(project);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath proofFolderPath = project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder proofFolder = root.getFolder(proofFolderPath);
      if(proofFolder.exists()){
         LinkedList<IFile> metaFiles = collectAllMetaFiles(proofFolder);
         for(IFile metaFile : metaFiles){
            metaFile.setHidden(hide);
            metaFile.refreshLocal(IResource.DEPTH_ZERO, null);
         }
      }
      project.refreshLocal(IResource.DEPTH_INFINITE, null);
   }
   
   
   /**
    * Returns a {@link LinkedList} with all Java source folders ais {@link IPath}.
    * @param project - the project to search the source folders for.
    * @return the {@link LinkedList} with the source folders.
    * @throws JavaModelException
    */
   public static LinkedList<IPath> getAllJavaSrcFolders(IProject project) throws JavaModelException{
      LinkedList<IPath> srcFolders = new LinkedList<IPath>();

      IJavaProject javaProject = JavaCore.create(project);
      IClasspathEntry[] classpathEntries = javaProject.getResolvedClasspath(true);
      
      for(int i = 0; i<classpathEntries.length;i++){
         IClasspathEntry entry = classpathEntries[i];
         if(entry.getContentKind() == IPackageFragmentRoot.K_SOURCE){
            IPath path = entry.getPath();
            srcFolders.add(path);
         }
      }
      return srcFolders;
   }

   /**
    * Checks if the given {@link IFolder} is the proof folder of a KeY project.
    * @param element The {@link IFolder} to check.
    * @return {@code true} is proof folder of a KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isProofFolder(IFolder element) throws CoreException {
      return element != null &&
             PROOF_FOLDER_NAME.equals(element.getName()) &&
             element.getParent() instanceof IProject &&
             isKeYProject(element.getProject());
   }
   
   /**
    * Checks if the given {@link IProject} is a KeY project.
    * @param project The {@link IProject} to check.
    * @return {@code true} is KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isKeYProject(IProject project) throws CoreException {
      return project != null &&
             project.hasNature(KeYProjectNature.NATURE_ID);
   }
}