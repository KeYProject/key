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
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
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
      if (delta != null && KeYProjectProperties.isEnableBuildProofs(project)) {
         ProofManager proofManager = null;
         try {
            proofManager = new ProofManager(project);
            
            if (!KeYProjectProperties.isEnableBuildProofsEfficient(project)) {
               proofManager.runProofs(monitor);
            }
            else {
               LinkedList<IFile> changedJavaFiles = collectChangedJavaFiles(delta);
               proofManager.runProofs(changedJavaFiles, monitor);
            }
         }
         catch (Exception e){
           LogUtil.getLogger().createErrorStatus(e); // TODO: Does nothing, you should throw a CoreException: throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
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
         proofManager.clean(monitor);
         super.clean(monitor);
      }
      catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e); // TODO: Does nothing, you should throw a CoreException: throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
      finally {
         if (proofManager != null) {
            proofManager.dispose();
         }
      }
   }
   
   
   /**
    * Collects all {@link IResourceDelta#ADDED} and {@link IResourceDelta#CHANGED} java files in the given {@link IResourceDelta}. 
    * @param delta - the {@link IResourceDelta} to use
    * @return a {@link LinkedList} with the collected java{@link IFile}s
    * @throws Exception
    */
   private LinkedList<IFile> collectChangedJavaFiles(IResourceDelta delta) throws Exception{      
      KeYProjectResourceDeltaVisitor deltaVisitor = new KeYProjectResourceDeltaVisitor();
      delta.accept(deltaVisitor);
      
      LinkedList<IFile> deltasFiles = new LinkedList<IFile>();
      IFile file = null;
      LinkedList<IResourceDelta> deltaList = deltaVisitor.getDeltaList();
      for(IResourceDelta aDelta : deltaList){
         try{
            // TODO: What happens if a proof file has changed? Marker and meta file should be updated based on the new proof result.
            // TODO: What happens if a meta file is modified by a user?  
            switch(aDelta.getKind()){
            case IResourceDelta.ADDED:
               file = getFile(aDelta.getResource());
               if(file != null && !deltasFiles.contains(file)){
                  deltasFiles.add(file);
               }
               break;
            case IResourceDelta.CHANGED:
               file = getFile(aDelta.getResource());
               if(file != null && !deltasFiles.contains(file)){
                  deltasFiles.add(file);
               }
               break;
            }
            // TODO: Why not when a resource is deleted?
         } catch (Exception e) {
            LogUtil.getLogger().createErrorStatus(e); // TODO: Does nothing. What happens if a single file can't be processed? Continue build or throw exception? It might be bedder to throw an exception!?
         }
      }
      return deltasFiles;
   }
   
   
   /**
    * Returns the {@link IFile} if the given {@link IResource} is in the source{@link IFolder}, {@link IResource#FILE} and a java file.
    * @param res - the {@link IResource} to use
    * @return the {@link IFile}
    * @throws Exception
    */
   private IFile getFile(IResource res) throws Exception{ // TODO: This implementation does not work in general. What if the project has no src folder or if it is named different? Use JDT functionality instead like in KeYUtil#updateToMethodNameLocation(...).  
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