package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.swt.SWTUtil;

public class ProofManagerJob extends Job {

   public static final String PROOFMANAGERJOB_FAMILY = "proofManagerJobFamily";
   public final static  MutexRule mutex = new MutexRule();
   
   public ProofManagerJob(String name) {
      super(name);
      setRule(mutex);
   }

   @Override
   protected IStatus run(IProgressMonitor monitor) {
//   public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException {
      try {
         for(int i = 0; i<1000; i++){
            SWTUtil.checkCanceled(monitor);
            long start = System.currentTimeMillis();
            while(System.currentTimeMillis() < start + 10000){
            }
            System.out.println("runs" + i);
         }
         return Status.OK_STATUS;
      }
      catch (OperationCanceledException e) {
         return Status.CANCEL_STATUS;
      }
   }
   
   @Override
   public boolean belongsTo(Object family) {
      return PROOFMANAGERJOB_FAMILY == family;
   }
}
