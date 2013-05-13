/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.test.testcase;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.junit.Test;
import org.key_project.util.eclipse.JobUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Tests for {@link JobUtil}.
 * @author Martin Hentschel
 */
public class JobUtilTest extends TestCase {
   /**
    * Tests {@link JobUtil#cancel(Job[])}.
    */
   @Test
   public void testCancel() {
      Job firstJob = new EndlessJob();
      Job secondJob = new EndlessJob();
      firstJob.schedule();
      secondJob.schedule();
      Job[] jobs = new Job[] {firstJob, secondJob};
      JobUtil.cancel(jobs);
      JobUtil.waitFor(jobs, 20);
      assertEquals(Job.NONE, firstJob.getState());
      assertEquals(Job.NONE, secondJob.getState());
   }
   
   /**
    * A {@link Job} which is endless running.
    * @author Martin Hentschel
    */
   private static class EndlessJob extends Job {
      /**
       * Constructor.
       */
      public EndlessJob() {
         super("Endless Job");
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected IStatus run(IProgressMonitor monitor) {
         try {
            while (true) {
               try {
                  SWTUtil.checkCanceled(monitor);
                  Thread.sleep(10);
               }
               catch (InterruptedException e) {
                  // Nothing to do
               }
            }
         }
         catch (OperationCanceledException e) {
            return Status.CANCEL_STATUS;
         }
      }
   }
   
   /**
    * Tests {@link JobUtil#waitFor(Job[], int)}.
    */
   @Test
   public void testWaitFor_array() {
      // Test null
      JobUtil.waitFor((Job[])null, 50); // No exception, dead lock expected.
      // Test valid job
      Job firstJob = new WaitForJob();
      Job secondJob = new WaitForJob();
      Job[] jobs = {firstJob, secondJob};
      firstJob.schedule();
      secondJob.schedule();
      assertNotSame(Job.NONE, firstJob.getState());
      assertNotSame(Job.NONE, secondJob.getState());
      JobUtil.waitFor(jobs, 50);
      assertSame(Job.NONE, firstJob.getState());
      assertSame(Job.NONE, secondJob.getState());
   }
   
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