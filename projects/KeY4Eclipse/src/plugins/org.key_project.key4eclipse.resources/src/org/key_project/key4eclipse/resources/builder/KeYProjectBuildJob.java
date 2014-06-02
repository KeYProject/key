package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class KeYProjectBuildJob extends Job{

   private IProject project;
      
   public KeYProjectBuildJob(String name, IProject project){
      super(name);
      this.project = project;
   }
   
   @Override
   public boolean belongsTo(Object family) {
      return "KeYProjectBuildJob".equals(family);
   }

   @Override
   protected IStatus run(IProgressMonitor monitor) {
      ProofManager proofManager = null;
      try{
         proofManager = new ProofManager(project);
         proofManager.runProofs(monitor);
      } catch (Exception e){
         //TODO
         System.out.println("Error");
      }
      finally{
         if(proofManager != null){
          proofManager.dispose();
         }
      }
      
//      int i = 0;
//      KeYProjectBuilder.changedJavaFiles = new LinkedList<IFile>();
//      KeYProjectBuilder.jobChangedFiles = new LinkedList<IFile>();
//      IFolder proofFolder = project.getFolder("proofs");
////      IResourceRuleFactory rf = ResourcesPlugin.getWorkspace().getRuleFactory();
////      ISchedulingRule rule = rf.createRule(proofFolder);
//      if(!proofFolder.exists()){
//         try {
////            Job.getJobManager().beginRule(rule, null);
//            proofFolder.create(true, false, null);
//         }
//         catch (CoreException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//         }
//         finally{
////            Job.getJobManager().endRule(rule);
//         }
//      }
//      while(!monitor.isCanceled()){
//         System.out.println(i);
//         IFile file = proofFolder.getFile(""+i);
//         KeYProjectBuilder.jobChangedFiles.add(file);
//         i++;
//         try {
//            if(file.exists()){
//               file.delete(true, null);
//            } else {
//               file.create(null, true, null);
//            }
//         } catch (CoreException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//         }
//         long time = System.currentTimeMillis();
//         while(time + 1000 > System.currentTimeMillis()){
//            
//         }
//      }
      return Status.OK_STATUS;
   }

}
