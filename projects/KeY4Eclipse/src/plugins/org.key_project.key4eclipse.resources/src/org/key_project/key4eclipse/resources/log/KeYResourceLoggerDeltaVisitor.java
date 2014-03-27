package org.key_project.key4eclipse.resources.log;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;

public class KeYResourceLoggerDeltaVisitor implements IResourceDeltaVisitor{

   private LinkedList<String> chagedFiles = new LinkedList<String>();
   private LinkedList<String> addedFiles = new LinkedList<String>();
   private LinkedList<String> removedFiles = new LinkedList<String>();
   
   
   @Override
   public boolean visit(IResourceDelta delta) throws CoreException {
      IResource res = delta.getResource();
      if(res.getType() == IResource.FILE){
         if(IResourceDelta.CHANGED == delta.getKind()){
            IFile file = (IFile) res;
            if(!"class".equals(file.getFileExtension())){
               chagedFiles.add(""+file.getFullPath());
            }
            
         }
         else if(IResourceDelta.ADDED == delta.getKind()){
            IFile file = (IFile) res;
            if(!"class".equals(file.getFileExtension())){
               addedFiles.add(""+file.getFullPath());
            }
            
         }
         else if(IResourceDelta.REMOVED == delta.getKind()){
            IFile file = (IFile) res;
            if(!"class".equals(file.getFileExtension())){
               removedFiles.add(""+file.getFullPath());
            }
            
         }
         
         
      }
      return true;
   }

   public LinkedList<String> getChagedFiles() {
      return chagedFiles;
   }

   public LinkedList<String> getAddedFiles() {
      return addedFiles;
   }

   public LinkedList<String> getRemovedFiles() {
      return removedFiles;
   }


}
