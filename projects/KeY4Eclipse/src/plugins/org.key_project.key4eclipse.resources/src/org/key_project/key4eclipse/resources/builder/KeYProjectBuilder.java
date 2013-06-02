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
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.LogUtil;

public class KeYProjectBuilder extends IncrementalProjectBuilder {

   public final static String BUILDER_ID = "org.key_project.key4eclipse.resources.KeYProjectBuilder";
   private static boolean initialBuildDone = false;
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      IResourceDelta delta = getDelta(project);
      if (delta != null && KeYProjectProperties.isBuildProofs(project)) {
         ProofManager proofManager = null;
         try {
            proofManager = new ProofManager(project);
            
            boolean enableEfficientProofManagement = KeYProjectProperties.isEnableEfficientProofManagement(project);
            boolean autoDeleteProofFiles = KeYProjectProperties.isAutoDeleteProofFiles(project); 
            
            if (!enableEfficientProofManagement || !initialBuildDone) {
               proofManager.runAllProofs(autoDeleteProofFiles);
               initialBuildDone = true;
               System.out.println("ALL");
            }
            else if(enableEfficientProofManagement && initialBuildDone){
               //Do not use. Not working right now.
//               runProofsEfficient(proofManager, delta);
               LinkedList<IFile> changedJavaFiles = collectChangedJavaFiles(delta);
               proofManager.runProofsSelective(changedJavaFiles, autoDeleteProofFiles);
               System.out.println("EFFICIENT");
            }
         }
         catch (Exception e){
           LogUtil.getLogger().createErrorStatus(e);
         }
         finally {
            if (proofManager != null) {
               proofManager.dispose();
            }
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
      ProofManager proofManager = null;
      try {
         proofManager = new ProofManager(project);
         proofManager.clean(KeYProjectProperties.isAutoDeleteProofFiles(project));
         super.clean(monitor);
      }
      catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
      finally {
         if (proofManager != null) {
            proofManager.dispose();
         }
      }
   }
   
   
   private LinkedList<IFile> collectChangedJavaFiles(IResourceDelta delta) throws Exception{      
      KeYProjectResourceDeltaVisitor deltaVisitor = new KeYProjectResourceDeltaVisitor();
      delta.accept(deltaVisitor);
      
      LinkedList<IFile> deltasFiles = new LinkedList<IFile>();
      IFile file = null;
      LinkedList<IResourceDelta> deltaList = deltaVisitor.getDeltaList();
      for(IResourceDelta aDelta : deltaList){
         try{
            switch(aDelta.getKind()){
            case IResourceDelta.ADDED:
               file = handleAdded(aDelta.getResource());
               if(file != null && !deltasFiles.contains(file)){
                  deltasFiles.add(file);
               }
               break;
//            case IResourceDelta.REMOVED:
//               file = handleRemoved(aDelta.getResource());
//               if(file != null && !deltasFiles.contains(file)){
//                  deltasFiles.add(file);
//               }
//               break;
            case IResourceDelta.CHANGED:
               file = handleChanged(aDelta.getResource());
               if(file != null && !deltasFiles.contains(file)){
                  deltasFiles.add(file);
               }
               break;
            }
         } catch (Exception e) {
            LogUtil.getLogger().createErrorStatus(e);
         }
      }
      return deltasFiles;
   }
   
   
   /**
    * Handles the proofManagement for added {@link IResource}s
    * @param proofManager The {@link ProofManager} to use.
    * @param res - the added {@link IResource}
    * @throws Exception
    */
   private IFile handleAdded(IResource res) throws Exception{
      if(res.exists()){
         IPath resourcePath = res.getFullPath();
         IPath sourceFolderPath = res.getProject().getFullPath().append("src");
         //Resource was added in the ProofFolder
         if(sourceFolderPath.isPrefixOf(resourcePath)){
            if(res.getType() == IResource.FILE){
               //addedResoure has a fileExtension
               if(res.getFileExtension() != null){
                  //addedResoure is a JavaFile
                  if(res.getFileExtension().equalsIgnoreCase("java")){
                     return (IFile) res;
                  }
               }
            }
         }         
      }
      return null;
   }
   
   
//   /**
//    * Handles the proofManagement for removed {@link IResource}s
//    * @param proofManager The {@link ProofManager} to use.
//    * @param res - the removed {@link IResource}
//    * @throws Exception
//    */
//   private IFile handleRemoved(ProofManager proofManager, IResource res) throws Exception{
//      
//      return null;
//   }
   
   
   /**
    * Handles the proofManagement for changed {@link IResource}s
    * @param proofManager The {@link ProofManager} to use.
    * @param res - the changed {@link IResource}
    * @throws Exception
    */
   private IFile handleChanged(IResource res) throws Exception{
      if(res.exists()){
         IPath resourcePath = res.getFullPath();
         IPath sourceFolderPath = res.getProject().getFullPath().append("src");
         //Resource was added in the ProofFolder
         if(sourceFolderPath.isPrefixOf(resourcePath)){
            //changedResoure is a File
            if(res.getType() == IResource.FILE){
               //changedResoure has a fileExtension
               if(res.getFileExtension() != null){
                  //changedResoure is a JavaFile
                  if(res.getFileExtension().equalsIgnoreCase("java")){
                     return (IFile) res;
                  }
               }
            }
         }
      }
      return null;
   }
}
