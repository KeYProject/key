package org.key_project.util.test.testcase;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.junit.Test;
import org.key_project.util.eclipse.JobUtil;

/**
 * Tests for {@link JobUtil}.
 * @author Martin Hentschel
 */
public class JobUtilTest extends TestCase {
   /**
    * Tests {@link JobUtil#waitFor(Iterable, int)}.
    */
   @Test
   public void testWaitFor_Iterable() {
      // Test null
      JobUtil.waitFor((Iterable<Job>)null, 50); // No exception, dead lock expected.
      // Test valid job
      List<Job> jobs = new LinkedList<Job>();
      Job firstJob = new WaitForJob();
      Job secondJob = new WaitForJob();
      jobs.add(firstJob);
      jobs.add(secondJob);
      firstJob.schedule();
      secondJob.schedule();
      assertNotSame(Job.NONE, firstJob.getState());
      assertNotSame(Job.NONE, secondJob.getState());
      JobUtil.waitFor(jobs, 50);
      assertSame(Job.NONE, firstJob.getState());
      assertSame(Job.NONE, secondJob.getState());
   }
   
   /**
    * Tests {@link JobUtil#waitFor(org.eclipse.core.runtime.jobs.Job, int)}.
    */
   @Test
   public void testWaitFor_Job() {
      // Test null
      JobUtil.waitFor((Job)null, 50); // No exception, dead lock expected.
      // Test valid job
      Job job = new WaitForJob();
      job.schedule();
      assertNotSame(Job.NONE, job.getState());
      JobUtil.waitFor(job, 50);
      assertSame(Job.NONE, job.getState());
   }
   
   /**
    * A {@link Job} which does nothing.
    * @author Martin Hentschel
    */
   private static class WaitForJob extends Job {
      /**
       * Constructor.
       */
      public WaitForJob() {
         super("Job to wait for");
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      protected IStatus run(IProgressMonitor monitor) {
         try {
            Thread.sleep(200);
         }
         catch (InterruptedException e) {
         }
         return Status.OK_STATUS;
      }
   }
}
