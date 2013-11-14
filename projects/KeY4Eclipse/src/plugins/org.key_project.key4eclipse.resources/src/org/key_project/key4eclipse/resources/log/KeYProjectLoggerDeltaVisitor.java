package org.key_project.key4eclipse.resources.log;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;

public class KeYProjectLoggerDeltaVisitor implements IResourceDeltaVisitor{

   private int changedFiles = 0;
   private int addedFiles = 0;
   private int removedFiles = 0;

   private String chagedFilesStr = "";
   private String addedFilesStr = "";
   private String removedFilesStr = "";
   
   
   @Override
   public boolean visit(IResourceDelta delta) throws CoreException {
      IResource res = delta.getResource();
      if(res.getType() == IResource.FILE){
         if(IResourceDelta.CHANGED == delta.getKind()){
            IFile file = (IFile) res;
            if(!"class".equals(file.getFileExtension())){
               changedFiles++;
               chagedFilesStr += file.getFullPath() + "\n";
            }
            
         }
         else if(IResourceDelta.ADDED == delta.getKind()){
            IFile file = (IFile) res;
            if(!"class".equals(file.getFileExtension())){
               addedFiles++;
               addedFilesStr += file.getFullPath() + "\n";
            }
            
         }
         else if(IResourceDelta.REMOVED == delta.getKind()){
            IFile file = (IFile) res;
            if(!"class".equals(file.getFileExtension())){
               removedFiles++;
               removedFilesStr += file.getFullPath() + "\n";
            }
            
         }
         
         
      }
      return true;
   }

   public int getChangedFiles() {
      return changedFiles;
   }

   public int getAddedFiles() {
      return addedFiles;
   }

   public int getRemovedFiles() {
      return removedFiles;
   }

   public String getChagedFilesStr() {
      return chagedFilesStr;
   }

   public String getAddedFilesStr() {
      return addedFilesStr;
   }

   public String getRemovedFilesStr() {
      return removedFilesStr;
   }


}
