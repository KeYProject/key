/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

import junit.framework.TestCase;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.job.ScheduledJobCollector;
import org.key_project.util.java.IFilter;

/**
 * Tests for {@link ScheduledJobCollector}.
 * @author Martin Hentschel
 */
public class ScheduledJobCollectorTest extends TestCase {
   /**
    * Tests the collection process initially with an
    * {@link IFilter} and later without an {@link IFilter} and again with an
    * {@link IFilter}.
    */
   public void testInitialFilter() {
      // Create collector
      IFilter<Job> filter = new IFilter<Job>() {
         @Override
         public boolean select(Job element) {
            return !"B".equals(element.getName()) &&
                   !"F".equals(element.getName()) &&
                   !"H".equals(element.getName());
         }
      };
      ScheduledJobCollector collector = new ScheduledJobCollector(filter);
      assertJobs(collector);
      assertEquals(filter, collector.getFilter());
      // Test no jobs
      collector.start();
      collector.stop();
      assertJobs(collector);
      // Test jobs without filter
      collector.start();
      new EmptyJob("A").schedule();
      new EmptyJob("B").schedule();
      new EmptyJob("C").schedule();
      collector.stop();
      new EmptyJob("D").schedule();
      assertJobs(collector, "A", "C");
      // Remove filter
      collector.setFilter(null);
      assertNull(collector.getFilter());
      collector.start();
      new EmptyJob("E").schedule();
      new EmptyJob("F").schedule();
      new EmptyJob("G").schedule();
      collector.stop();
      new EmptyJob("H").schedule();
      new EmptyJob("I").schedule();
      assertJobs(collector, "E", "F", "G");
      // Set filter
      collector.setFilter(filter);
      assertEquals(filter, collector.getFilter());
      collector.start();
      new EmptyJob("E").schedule();
      new EmptyJob("F").schedule();
      new EmptyJob("G").schedule();
      collector.stop();
      new EmptyJob("H").schedule();
      new EmptyJob("I").schedule();
      assertJobs(collector, "E", "G");
   }
   
   /**
    * Tests the collection process initially without an
    * {@link IFilter} and later with an {@link IFilter} and again without an
    * {@link IFilter}.
    */
   public void testInitialNoFilter() {
      // Create collector
      ScheduledJobCollector collector = new ScheduledJobCollector();
      assertJobs(collector);
      assertNull(collector.getFilter());
      // Test no jobs
      collector.start();
      collector.stop();
      assertJobs(collector);
      // Test jobs without filter
      collector.start();
      new EmptyJob("A").schedule();
      new EmptyJob("B").schedule();
      new EmptyJob("C").schedule();
      collector.stop();
      new EmptyJob("D").schedule();
      assertJobs(collector, "A", "B", "C");
      // Define filter
      IFilter<Job> filter = new IFilter<Job>() {
         @Override
         public boolean select(Job element) {
            return !"F".equals(element.getName()) &&
                   !"H".equals(element.getName());
         }
      };
      collector.setFilter(filter);
      assertEquals(filter, collector.getFilter());
      collector.start();
      new EmptyJob("E").schedule();
      new EmptyJob("F").schedule();
      new EmptyJob("G").schedule();
      collector.stop();
      new EmptyJob("H").schedule();
      new EmptyJob("I").schedule();
      assertJobs(collector, "E", "G");
      // Remove filter
      collector.setFilter(null);
      assertNull(collector.getFilter());
      collector.start();
      new EmptyJob("E").schedule();
      new EmptyJob("F").schedule();
      new EmptyJob("G").schedule();
      collector.stop();
      new EmptyJob("H").schedule();
      new EmptyJob("I").schedule();
      assertJobs(collector, "E", "F", "G");
   }
   
   /**
    * Makes sure that the correct jobs are found.
    * @param collector The {@link ScheduledJobCollector} which provides the jobs.
    * @param expectedJobNames The expected {@link Job} names.
    */
   protected void assertJobs(ScheduledJobCollector collector, String... expectedJobNames) {
      assertNotNull(collector);
      Job[] jobs = collector.getJobs();
      assertNotNull(jobs);
      assertEquals(expectedJobNames.length, jobs.length);
      for (int i = 0; i < expectedJobNames.length; i++) {
         assertEquals(expectedJobNames[i], jobs[i].getName());
      }
      collector.clearJobs();
   }
   
   /**
    * A {@link Job} which does nothing.
    * @author Martin Hentschel
    */
   private static class EmptyJob extends Job {
      /**
       * Constructor. 
       * @param name The name of this {@link Job}.
       */
      public EmptyJob(String name) {
         super(name);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected IStatus run(IProgressMonitor monitor) {
         return Status.OK_STATUS;
      }
   }
}