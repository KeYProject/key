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

package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaCore;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * DeltaVisitor to visit every child of the given delta and extract KeY Project relevant changes.
 * @author Stefan Käsdorf
 */
public class KeYProjectDeltaVisitor implements IResourceDeltaVisitor{

   private List<IFile> changedJavaFiles;
   private List<IFile> changedProofAndMetaFiles;
   private List<IPath> srcFolders;
   
   public KeYProjectDeltaVisitor(IProject project) {
      this.changedJavaFiles = new LinkedList<IFile>();
      this.changedProofAndMetaFiles = new LinkedList<IFile>();
      srcFolders = KeYResourcesUtil.getAllJavaSrcFolders(project);
   }

   public List<IFile> getChangedJavaFiles(){
      return changedJavaFiles;
   }
   
   public List<IFile> getChangedProofAndMetaFiles(){
      return changedProofAndMetaFiles;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(IResourceDelta delta) {
      IResource deltaRes = delta.getResource();
      if(IResource.FILE == deltaRes.getType()){
         if(isJavaFileAndInSrcFolder(deltaRes)){
            if(IResourceDelta.ADDED == delta.getKind() || IResourceDelta.CHANGED == delta.getKind() || IResourceDelta.REMOVED == delta.getKind()){
               if(!changedJavaFiles.contains(deltaRes)){
                  changedJavaFiles.add((IFile) deltaRes);
               }
            }
         }
         else if(isProofOrMetaFile(deltaRes)){
            if(!changedProofAndMetaFiles.contains(deltaRes)){
               changedProofAndMetaFiles.add((IFile) deltaRes);
            }
         }
      }
      return true;
   }

   
   /**
    * Checks if the given {@link IResource} is a java file and if it is stored in a source folder.
    * @param res - the {@link IResource} to be checked
    * @return true if the given {@link IResource} is a java file and is stored in a source folder.
    */
   private boolean isJavaFileAndInSrcFolder(IResource res){
      if(res.exists() && IResource.FILE == res.getType() && isInSourceFolder(res, srcFolders)){
         IJavaElement element = JavaCore.create(res);
         if (element instanceof ICompilationUnit) {
            return true;
         }
      }
      return false;
   }
   
   
   /**
    * Checks if the given {@link IResource} is a proof or a meta file and if it is stored in the proof folder of the project.
    * @param res - the {@link IResource} to be checked
    * @return true if the given {@link IResource} is a proof or a meta file and if it is stored in the proof folder of the project.
    */
   private boolean isProofOrMetaFile(IResource res){
      if(IResource.FILE == res.getType()){
         IPath proofFolder = res.getProject().getFullPath().append("proofs");
         return proofFolder.isPrefixOf(res.getFullPath());
      }
      return false;
   }
   

   /**
    * Checks if the given {@link IResource} is stored in a source folder.
    * @param res - the {@link IResource} to be checked
    * @param srcFolders - the source folders
    * @return true if the given {@link IResource} is stored in a source folder.
    */
   private boolean isInSourceFolder(IResource res, List<IPath> srcFolders){
      for(IPath path : srcFolders){
         if(path.isPrefixOf(res.getFullPath())){
            return true;
         }
      }
      return false;
   }
}