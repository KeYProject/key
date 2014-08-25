package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.resources.util.EditorSelection;
import org.key_project.key4eclipse.resources.util.EditorSelector;

public class KeYProjectBuildJob extends Job{

   private IProject project;
   private EditorSelection editorSelection;
   private KeYProjectBuildInstruction inst;
      
   public KeYProjectBuildJob(String name, IProject project, KeYProjectBuildInstruction inst){
      super(name);
      this.project = project;
      editorSelection = new EditorSelector().getEditorSelection();
      this.inst = inst;
   }
   
   
   public IProject getProject(){
      return project;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean belongsTo(Object family) {
      return "KeYProjectBuildJob".equals(family);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(IProgressMonitor monitor) {
      ProofManager proofManager = null;
      try{
         proofManager = new ProofManager(project);
         proofManager.runProofs(monitor, editorSelection, inst);
      } catch (Exception e){
         //TODO
         System.out.println("Error");
      }
      finally{
         if(proofManager != null){
          proofManager.dispose();
         }
      }
      return Status.OK_STATUS;
   }

}
