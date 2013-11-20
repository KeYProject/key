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

import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

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
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;

/**
 * @author Stefan Käsdorf
 */
public class KeY4EclipseResourcesUtil {
   
   
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
      LinkedList<IFile> metaFileList = new LinkedList<IFile>();
//      folder.accept(new IResourceVisitor() {
//         @Override
//         public boolean visit(IResource resource) throws CoreException {
//            return false;
//         }
//      }, IResource.DEPTH_INFINITE, true); // TODO: It is not efficient to iterate recursive over IResources. Use the visitor pattern instead as in this uncommented code.
      
      IResource[] members = folder.members(IContainer.INCLUDE_HIDDEN);
      for(IResource member : members){
         if(member.getType() == IResource.FILE){
            IFile file = (IFile) member;
            if("meta".equalsIgnoreCase(file.getFileExtension())){ //TODO: Create constant for file extension meta and use it everywhere
               metaFileList.add(file);
            }
         }
         else if(member.getType() == IResource.FOLDER){
            IFolder subFolder = (IFolder) member;
            metaFileList.addAll(collectAllMetaFiles(subFolder));
         }
      }
      return metaFileList;
   }
   
   
   /**
    * Computes the MD5 Sum for the given {@link IFile} content.
    * @param iFile - the {@link IFile} to use
    * @return the MD5 Sum as {@link String}
    */
   public static String computeContentMD5(IFile iFile){ // TODO: Move to ResourceUtil.computeMD5(IFile)
      try {
         return IOUtil.computeMD5(iFile.getContents());
      }
      catch(Exception e) {
         throw new RuntimeException("Unable to process file for MD5", e); // TODO: Bad idea, it is legal that exceptions are thrown, treat it by the caller of this method!
      }
   }
   
   
   /**
    * Checks if the given {@link KeYJavaType} is part of the project or an external resource.
    * @param kjt - the {@link KeYJavaType} to use
    * @return false if the {@link KeYJavaType} is an internal resource
    */
   public static boolean filterKeYJavaType(KeYJavaType kjt){ // TODO: Use KeYTypeUtil.isLibraryClass(...) instead after pull from master
      if (!(kjt.getJavaType() instanceof ClassDeclaration || 
            kjt.getJavaType() instanceof InterfaceDeclaration) || 
          ((TypeDeclaration)kjt.getJavaType()).isLibraryClass()) {
         return true;
      }
      return false;
   }
   
   
   /**
    * Filters the given {@link Set} of {@link KeYJavaType}s and sorts them.
    * @param kjts - the {@link KeYJavaType}s to filter and sort
    * @return the filtered and sorted {@link KeYJavaType[]}
    */
   public static KeYJavaType[] sortKeYJavaTypes(Set<KeYJavaType> kjts){ // TODO: Move to KeYUtil.sortKeYJavaTypes(Set<KeYJavaType>)
      Iterator<KeYJavaType> it = kjts.iterator();
      while (it.hasNext()) {
         KeYJavaType kjt = it.next();
         if (filterKeYJavaType(kjt)) {
            it.remove();
         }
      }
      KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
      Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
         public int compare(KeYJavaType o1, KeYJavaType o2) {
            return o1.getFullName().compareTo(o2.getFullName());
         }
      });
      return kjtsarr;
   }
   
   
   /**
    * Applies the {@link KeYProjectProperties#PROP_HIDE_META_FILES} to all metaFiles in the given {@link IProject}.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void hideMetaFiles(IProject project) throws CoreException{
      boolean hide = KeYProjectProperties.isHideMetaFiles(project);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath proofFolderPath = project.getFullPath().append("proofs"); // TODO: Make a constant for folder name "proofs" and use it everywhere
      IFolder proofFolder = root.getFolder(proofFolderPath);
      if(proofFolder.exists()){
         LinkedList<IFile> metaFiles = collectAllMetaFiles(proofFolder);
         for(IFile metaFile : metaFiles){
            metaFile.setHidden(hide);
            //TODO: refresh gui
         }
      }
      project.refreshLocal(IResource.DEPTH_INFINITE, null);
   }
}