package org.key_project.key4eclipse.resources.builder;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.key_project.key4eclipse.resources.io.LastChangesFileReader;
import org.key_project.key4eclipse.resources.io.LastChangesFileWriter;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

/**
 * Delta for KeY Projects. Required to track changes between interruptible builds.
 * @author Stefan Käsdorf
 */
public class KeYProjectDelta {

   private IProject project;
   private Set<IFile> changedJavaFiles;
   private Set<IFile> changedProofAndMetaFiles;
   private Set<IFile> jobChangedFiles;
   private boolean isBuilding;
   public final Object lock;
   
   public KeYProjectDelta(IProject project){
      this.project = project;
      this.isBuilding = false;
      this.lock = new Object();
      changedJavaFiles = new LinkedHashSet<IFile>();
      changedProofAndMetaFiles = new LinkedHashSet<IFile>();
      jobChangedFiles = Collections.synchronizedSet(new LinkedHashSet<IFile>());
   }
   
   public Set<IFile> getChangedJavaFiles(){
      return KeYResourcesUtil.cloneSet(changedJavaFiles);
   }
   
   private void addChangedProofAndMetaFiles(Set<IFile> newChangedProofAndMetaFiles){
      synchronized (jobChangedFiles) {
         for(IFile file : newChangedProofAndMetaFiles){
            if(!jobChangedFiles.contains(file)){
               changedProofAndMetaFiles.add(file);
            }
            else{
               jobChangedFiles.remove(file);
            }
         }
      }
   }
   
   public void addJobChangedFile(IFile file){
      synchronized (jobChangedFiles) {
         if(!jobChangedFiles.contains(file)){
            jobChangedFiles.add(file);
         }
      }
   }
   
   /**
    * Returns iff a new Build is required, dependent on the changed Java-, Proof-, and Meta-Files.
    * @return true if a new Build is required
    */
   public boolean isBuildRequired(){
      synchronized(lock){
         if(!isBuilding && (!changedJavaFiles.isEmpty() || !changedProofAndMetaFiles.isEmpty())){
            return true;
         }
         return false;
      }
   }
   
   public boolean isBuilding(){
      return isBuilding;
   }
   
   /**
    * Updates the {@link KeYProjectDelta} associated with given {@link IResourceDelta}.
    * @param delta - the {@link IResourceDelta} to use
    * @return returns true if the update was successful
    */
   public boolean update(IResourceDelta delta){
      synchronized (lock) {
         LastChangesFileReader lcfr = new LastChangesFileReader(project);
         changedJavaFiles = lcfr.getChangedJavaFiles();
         addChangedProofAndMetaFiles(lcfr.getCHangedProofAndMetaFiles());
         if(delta != null && project.equals(delta.getResource().getProject())){
            try{
               KeYProjectDeltaVisitor visitor = new KeYProjectDeltaVisitor();
               delta.accept(visitor);
               Set<IFile> newChangedJavaFiles = visitor.getChangedJavaFiles();
               Set<IFile> newChangedProofAndMetaFiles = visitor.getChangedProofAndMetaFiles();
               if(!newChangedJavaFiles.isEmpty() || !newChangedProofAndMetaFiles.isEmpty() || !KeYResourcesUtil.getProofFolder(project).getFile(KeYResourcesUtil.LAST_CHANGES_FILE).exists()){
                  changedJavaFiles.addAll(newChangedJavaFiles);
                  addChangedProofAndMetaFiles(newChangedProofAndMetaFiles);
                  LastChangesFileWriter.writeLastChangesFile(project, changedJavaFiles, changedProofAndMetaFiles);
               }
            }
            catch (Exception e){
               LogUtil.getLogger().logError(e);
               return false;
            }
         }
         return true;
      }
   }

   /**
    * Resets the {@link KeYProjectDelta}. Always called when a new Build starts.
    */
   public void resetDelta() {
      isBuilding = false;
      changedJavaFiles = new LinkedHashSet<IFile>();
      changedProofAndMetaFiles = new LinkedHashSet<IFile>();
      jobChangedFiles = Collections.synchronizedSet(new LinkedHashSet<IFile>());
   }
   
   public void setIsBuilding(boolean isBuilding){
      this.isBuilding = isBuilding;
   }
}