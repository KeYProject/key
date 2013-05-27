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
   
   private ProofManager proofManager;
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IResourceDelta delta = getDelta(getProject());
      if (delta != null) {
         try{
            proofManager = new ProofManager(getProject());
            if(!KeYProjectProperties.isEnableEfficientProofManagement(getProject())) {
//               proofManager.runAllProofs();
               proofManager.runAllProofsWithContractList();
            }
            else{
               //Do not use. Not working right now.
               runProofsEfficient(delta);
            }
            
         } catch (Exception e){
           LogUtil.getLogger().createErrorStatus(e);
         }
      }
      return null;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void clean(IProgressMonitor monitor) throws CoreException {
      try {
         proofManager = new ProofManager(getProject());
         proofManager.clean();
         super.clean(monitor);
      }
      catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
   }
   
   
   private void runProofsEfficient(IResourceDelta delta) throws Exception{      
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
            case IResourceDelta.REMOVED:
               file = handleRemoved(aDelta.getResource());
               if(file != null && !deltasFiles.contains(file)){
                  deltasFiles.add(file);
               }
               break;
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
      proofManager.runSelectedProofs(deltasFiles);
   }
   
   
   /**
    * Handles the proofManagement for added {@link IResource}s
    * @param res - the added {@link IResource}
    * @throws Exception
    */
   private IFile handleAdded(IResource res) throws Exception{
      if(res.exists()){
         IPath resourcePath = res.getFullPath();
         IPath proofFolderPath = res.getProject().getFullPath().append("Proofs");
         //Resource was added in the ProofFolder
         if(proofFolderPath.isPrefixOf(resourcePath)){
            if(res.exists()){
               proofManager.deleteResource(res);
            }
         }
         //addedResoure is a File
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
      return null;
   }
   
   
   /**
    * Handles the proofManagement for removed {@link IResource}s
    * @param res - the removed {@link IResource}
    * @throws Exception
    */
   private IFile handleRemoved(IResource res) throws Exception{
      
      //removedResoure is a File
      if(res.getType() == IResource.FILE){
         //removedResoure has a fileExtension
         if(res.getFileExtension() != null){
            //removedResoure is a JavaFile
            if(res.getFileExtension().equalsIgnoreCase("java")){
               proofManager.deleteProofFolderForJavaFile(res);
            }
            else if(res.getFileExtension().equalsIgnoreCase("proof")){
               return proofManager.getJavaFileForProofFile(res);
            }
         }
      }
      return null;
   }
   
   
   /**
    * Handles the proofManagement for changed {@link IResource}s
    * @param res - the changed {@link IResource}
    * @throws Exception
    */
   private IFile handleChanged(IResource res) throws Exception{
      if(res.exists()){
         //changedResoure is a File
         if(res.getType() == IResource.FILE){
            //changedResoure has a fileExtension
            if(res.getFileExtension() != null){
               //changedResoure is a JavaFile
               if(res.getFileExtension().equalsIgnoreCase("java")){
                  return (IFile) res;
               }
               else if(res.getFileExtension().equalsIgnoreCase("proof")){
                  IFile javaFile = proofManager.getJavaFileForProofFile(res);
                  res.delete(true, null);
                  return javaFile;
               }
            }
         }
      }
      return null;
   }
}
