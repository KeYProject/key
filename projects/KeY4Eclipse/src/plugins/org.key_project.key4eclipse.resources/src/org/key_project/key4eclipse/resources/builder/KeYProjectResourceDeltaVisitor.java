package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.key_project.key4eclipse.resources.util.LogUtil;

import de.uka.ilkd.key.proof.ProblemLoaderException;

public class KeYProjectResourceDeltaVisitor implements IResourceDeltaVisitor{

   private ProofManager proofManager;
   
   public KeYProjectResourceDeltaVisitor(IProject project) throws CoreException, ProblemLoaderException{
      proofManager = new ProofManager(project);
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(IResourceDelta delta) throws CoreException {
      try{
         switch(delta.getKind()){
         case IResourceDelta.ADDED:
            handleAdded(delta.getResource());
            break;
         case IResourceDelta.REMOVED:
            handleRemoved(delta.getResource());
            break;
         case IResourceDelta.CHANGED:
            handleChanged(delta.getResource());
            break;
         }
      } catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
      return true;
   }
   
   
   /**
    * Handles the proofManagement for added {@link IResource}s
    * @param res - the added {@link IResource}
    * @throws Exception
    */
   private void handleAdded(IResource res) throws Exception{
      
      IPath resourcePath = res.getFullPath();
      IPath proofFolderPath = res.getProject().getFullPath().append("Proofs");
      
      if(proofFolderPath.isPrefixOf(resourcePath)){
         proofManager.deleteResource(res);
      }
      //addedResoure is a File
      else if(res.getType() == IResource.FILE){
         //addedResoure has a fileExtension
         if(res.getFileExtension() != null){
            //addedResoure is a JavaFile
            if(res.getFileExtension().equalsIgnoreCase("java")){
               proofManager.runProofsForResource(res);
            }
         }
      }
   }
   
   
   /**
    * Handles the proofManagement for removed {@link IResource}s
    * @param res - the removed {@link IResource}
    * @throws Exception
    */
   private void handleRemoved(IResource res) throws Exception{
      
      //removedResoure is a File
      if(res.getType() == IResource.FILE){
         //removedResoure has a fileExtension
         if(res.getFileExtension() != null){
            //removedResoure is a JavaFile
            if(res.getFileExtension().equalsIgnoreCase("java")){
               proofManager.deleteProofFolderForJavaFile(res);
            }
            else if(res.getFileExtension().equalsIgnoreCase("proof")){
               proofManager.rerunProofsForDeletedProofFiles(res);
            }
         }
      }
   }
   
   
   /**
    * Handles the proofManagement for changed {@link IResource}s
    * @param res - the changed {@link IResource}
    * @throws Exception
    */
   private void handleChanged(IResource res) throws Exception{
      
    //changedResoure is a File
      if(res.getType() == IResource.FILE){
         //changedResoure has a fileExtension
         if(res.getFileExtension() != null){
            //changedResoure is a JavaFile
            if(res.getFileExtension().equalsIgnoreCase("java")){
               proofManager.deleteMarker(res);
               proofManager.runProofsForResource(res);
            }
         }
      }
   }

}
