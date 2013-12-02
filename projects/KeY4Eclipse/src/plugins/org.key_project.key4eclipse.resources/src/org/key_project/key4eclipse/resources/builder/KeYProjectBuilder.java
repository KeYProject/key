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
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

/**
 * The KeYProject builder.
 * @author Stefan Käsdorf
 */
public class KeYProjectBuilder extends IncrementalProjectBuilder {

   
   /**
    * The builder id.
    */
   public final static String BUILDER_ID = "org.key_project.key4eclipse.resources.KeYProjectBuilder";
 
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      IResourceDelta delta = getDelta(project);
      ProofManager proofManager = null;
      try{
         if(kind == IncrementalProjectBuilder.FULL_BUILD){
            proofManager = new ProofManager(project);
            proofManager.runProofs(monitor);
         }
         else if(kind == IncrementalProjectBuilder.AUTO_BUILD || kind == IncrementalProjectBuilder.INCREMENTAL_BUILD){
            if (delta != null && KeYProjectProperties.isEnableBuildProofs(project)) {
               proofManager = new ProofManager(project);
               if (!KeYProjectProperties.isEnableBuildRequiredProofsOnly(project)) {
                  proofManager.runProofs(monitor);
               }
               else {
                  LinkedList<IFile> changedJavaFiles = collectChangedJavaFiles(delta);
                  proofManager.runProofs(changedJavaFiles, monitor);
               }
            }
         }
      }
      catch (Exception e){
         LogUtil.getLogger().logError(e.getMessage());
      }
      finally {
         if (proofManager != null) {
            proofManager.dispose();
         }
      }
      return null;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void clean(IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      IFolder mainProofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME));
      if(mainProofFolder != null){
         mainProofFolder.delete(true, null);
      }
      super.clean(monitor);
   }
   
   
   /**
    * Collects all {@link IResourceDelta#ADDED} and {@link IResourceDelta#CHANGED} java files in the given {@link IResourceDelta}. 
    * @param delta - the {@link IResourceDelta} to use
    * @return a {@link LinkedList} with the collected java{@link IFile}s
    * @throws CoreException 
    * @throws Exception
    */
   private LinkedList<IFile> collectChangedJavaFiles(IResourceDelta delta) throws CoreException{      
      KeYProjectResourceDeltaVisitor deltaVisitor = new KeYProjectResourceDeltaVisitor();
      delta.accept(deltaVisitor);
      
      LinkedList<IFile> deltasFiles = new LinkedList<IFile>();
      IFile file = null;
      LinkedList<IPath> srcFolders = KeYResourcesUtil.getAllJavaSrcFolders(getProject());
      LinkedList<IResourceDelta> deltaList = deltaVisitor.getDeltaList();
      for(IResourceDelta aDelta : deltaList){
            // TODO: What happens if a meta file is modified by a user?  --> problem solved when meta files are read-only
            switch(aDelta.getKind()){
            case IResourceDelta.ADDED:
               file = getFile(aDelta.getResource(), srcFolders);
               if(file != null && !deltasFiles.contains(file)){
                  deltasFiles.add(file);
               }
               break;
            case IResourceDelta.CHANGED:
               file = getFile(aDelta.getResource(), srcFolders);
               if(file != null && !deltasFiles.contains(file)){
                  deltasFiles.add(file);
               }
               break;
            }
      }
      return deltasFiles;
   }
   
   
   /**
    * Returns the {@link IFile} if the given {@link IResource} is in the sourceFolder and if it is java file.
    * @param res - the {@link IResource} to use
    * @return the {@link IFile}
    * @throws JavaModelException 
    * @throws Exception
    */
   private IFile getFile(IResource res, LinkedList<IPath> srcFolders) throws JavaModelException{  
      if(res.exists() && IResource.FILE == res.getType() && isInSourceFolder(res, srcFolders)){
         IJavaElement element = JavaCore.create(res);
         if (element instanceof ICompilationUnit) {
            return (IFile) res;
         }
      }
      return null;
   }
   
   
   private boolean isInSourceFolder(IResource res, LinkedList<IPath> srcFolders){
      for(IPath path : srcFolders){
         if(path.isPrefixOf(res.getFullPath())){
            return true;
         }
      }
      return false;
   }
}