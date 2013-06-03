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
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

import sun.net.ProgressMonitor;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;

public class KeY4EclipseResourcesUtil {
   
   
   public static KeYJavaType[] sortKeYJavaTypes(Set<KeYJavaType> kjts){
      Iterator<KeYJavaType> it = kjts.iterator();
      while (it.hasNext()) {
         KeYJavaType kjt = it.next();
         if (!(kjt.getJavaType() instanceof ClassDeclaration || 
               kjt.getJavaType() instanceof InterfaceDeclaration) || 
             ((TypeDeclaration)kjt.getJavaType()).isLibraryClass()) {
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
    * Runs an {@link IncrementalProjectBuilder}s INCREMENTAL_BUILD for the given {@link IProject} and waits for the build to finish.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void cleanBuildProject(IProject project) throws CoreException{
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      IWorkspaceDescription desc = workspace.getDescription();
      if(desc.isAutoBuilding()){
         desc.setAutoBuilding(false);
         workspace.setDescription(desc);
         //build
         project.build(IncrementalProjectBuilder.CLEAN_BUILD, new NullProgressMonitor());
         //reset auto build
         desc.setAutoBuilding(true);
         workspace.setDescription(desc);
      }
      else{
         //build
         
         project.build(IncrementalProjectBuilder.CLEAN_BUILD, new NullProgressMonitor());
      }
   }
   
   
   public static void hideMetaFiles(IProject project, boolean hide) throws CoreException{
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath proofFolderPath = project.getFullPath().append("Proofs");
      IFolder proofFolder = root.getFolder(proofFolderPath);
      if(proofFolder.exists()){
         LinkedList<IFile> metaFiles = collectAllMetaFiles(proofFolder);
         for(IFile metaFile : metaFiles){
            metaFile.setHidden(hide);
            //TODO: refresh gui
         }
      }
   }

   
   private static LinkedList<IFile> collectAllMetaFiles(IFolder folder) throws CoreException{
      LinkedList<IFile> metaFileList = new LinkedList<IFile>();
      IResource[] members = folder.members(IContainer.INCLUDE_HIDDEN);
      for(IResource member : members){
         if(member.getType() == IResource.FILE){
            IFile file = (IFile) member;
            if(file.getFileExtension().equalsIgnoreCase("meta")){
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
}