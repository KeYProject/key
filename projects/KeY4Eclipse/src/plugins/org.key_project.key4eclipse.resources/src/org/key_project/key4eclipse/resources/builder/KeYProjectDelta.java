package org.key_project.key4eclipse.resources.builder;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * Delta for KeY Projects. Required to track changes between interruptible builds.
 * @author Stefan Käsdorf
 */
public class KeYProjectDelta {

   private List<IFile> changedJavaFiles;
   private List<IFile> changedProofAndMetaFiles;
   private List<IFile> jobChangedFiles;
   
   public KeYProjectDelta(){
      changedJavaFiles = new LinkedList<IFile>();
      changedProofAndMetaFiles = new LinkedList<IFile>();
      jobChangedFiles = Collections.synchronizedList(new LinkedList<IFile>());
   }
   
   public List<IFile> getChangedJavaFiles(){
      return KeYResourcesUtil.cloneList(changedJavaFiles);
   }
   
   public void setChangedJavaFiles(List<IFile> changedJavaFiles){
      this.changedJavaFiles = changedJavaFiles;
   }
   
   public void addChangedJavaFiles(List<IFile> newChangedjavaFiles){
      KeYResourcesUtil.mergeLists(changedJavaFiles, newChangedjavaFiles);
   }
   
   public void setChangedProofAndMetaFiles(List<IFile> changedProofAndMetaFiles){
      this.changedProofAndMetaFiles = changedProofAndMetaFiles;
   }
   
   public void addChangedProofAndMetaFiles(List<IFile> newChangedProofAndMetaFiles){
      for(IFile file : newChangedProofAndMetaFiles){
         if(!jobChangedFiles.contains(file)){
            if(!changedProofAndMetaFiles.contains(file)){
               changedProofAndMetaFiles.add(file);
            }
         }
         else{
            jobChangedFiles.remove(file);
         }
      }
   }
   
   public synchronized void addJobChangedFile(IFile file){
      if(!jobChangedFiles.contains(file)){
         jobChangedFiles.add(file);
      }
   }
   
   /**
    * Returns iff a new Build is required, dependent on the changed Java-, Proof-, and Meta-Files.
    * @return true if a new Build is required
    */
   public boolean isBuildRequired(){
      if(!changedJavaFiles.isEmpty() || !changedProofAndMetaFiles.isEmpty()){
         return true;
      }
      return false;
   }

   /**
    * Resets the {@link KeYProjectDelta}. Always called when a new Build starts.
    */
   public void reset() {
      changedJavaFiles = new LinkedList<IFile>();
      changedProofAndMetaFiles = new LinkedList<IFile>();
      jobChangedFiles = Collections.synchronizedList(new LinkedList<IFile>());
   }
}
