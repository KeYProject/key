package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.log.LogRecord;
import org.key_project.key4eclipse.resources.log.LogRecordKind;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.EditorSelection;
import org.key_project.key4eclipse.resources.util.EditorSelector;
import org.key_project.key4eclipse.resources.util.LogUtil;

public class KeYProjectBuildJob extends Job{
   public static final String JOB_FAMILY = "KeYProjectBuildJob";
   
   private final IProject project;
   private final EditorSelection editorSelection;
   private final KeYProjectBuildInstruction inst;
      
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
      return JOB_FAMILY.equals(family);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(IProgressMonitor monitor) {
      ProofManager proofManager = null;
      final long start = System.currentTimeMillis();
      final boolean onlyRequiredProofs = KeYProjectProperties.isEnableBuildRequiredProofsOnly(project);
      final int numberOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      final boolean enableThreading = KeYProjectProperties.isEnableMultiThreading(project);
      try{
         proofManager = new ProofManager(project);
         proofManager.runProofs(monitor, editorSelection, inst);
         return Status.OK_STATUS;
      } 
      catch (OperationCanceledException e) {
         return Status.CANCEL_STATUS;
      }
      catch (Exception e){
         return LogUtil.getLogger().createErrorStatus(e);
      }
      finally{
         if(proofManager != null){
          proofManager.dispose();
         }
         try {
            LogManager.getInstance().log(project, new LogRecord(LogRecordKind.JOB, start, System.currentTimeMillis() - start, onlyRequiredProofs, enableThreading, numberOfThreads));
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
      }
   }

}
