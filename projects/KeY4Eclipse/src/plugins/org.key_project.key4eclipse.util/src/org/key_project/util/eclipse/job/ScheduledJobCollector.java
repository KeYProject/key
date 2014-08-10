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

package org.key_project.util.eclipse.job;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.key_project.util.java.IFilter;

/**
 * <p>
 * This utility class is used to collect all started {@link Job}s after
 * calling {@link #start()} until {@link #stop()} was executed.
 * </p>
 * <p>
 * The collected {@link Job}s are accessible via {@link #getJobs()}.
 * </p>
 * <p>
 * It is possible to filter the {@link Job}s added to {@link #getJobs()} via
 * an defined {@link IFilter} ({@link #setFilter(IFilter)}) or by overwriding
 * {@link #selectJob(Job)}.
 * </p>
 * @author Martin Hentschel
 */
public class ScheduledJobCollector {
   /**
    * The found {@link Job}s.
    */
   private List<Job> jobs = Collections.synchronizedList(new LinkedList<Job>());
   
   /**
    * An optional {@link IFilter} to filter {@link Job}s added to {@link #getJobs()}.
    */
   private IFilter<Job> filter;

   /**
    * Listens for started jobs on {@link Job#getJobManager()}.
    */
   private IJobChangeListener listener = new JobChangeAdapter() {
      @Override
      public void scheduled(IJobChangeEvent event) {
         ScheduledJobCollector.this.scheduled(event);
      }
   };
   
   /**
    * Constructor.
    */
   public ScheduledJobCollector() {
   }

   /**
    * Constructor.
    * @param filter An optional {@link IFilter} to filter {@link Job}s added to {@link #getJobs()}.
    */
   public ScheduledJobCollector(IFilter<Job> filter) {
      this.filter = filter;
   }

   /**
    * Starts the {@link Job} collection.
    */
   public void start() {
      Job.getJobManager().addJobChangeListener(listener);
   }
   
   /**
    * When a new {@link Job} was started.
    * @param event The event.
    */
   protected void scheduled(IJobChangeEvent event) {
      Job job = event.getJob(); 
      if (selectJob(job)) {
         synchronized (jobs) {
            jobs.add(job);
         }
      }
   }
   
   /**
    * Filters {@link Job}s added to {@link #getJobs()}.
    * @param job The {@link Job} to check.
    * @return {@code true} add to {@link #getJobs()}, {@code false} do not add to {@link #getJobs()}.
    */
   protected boolean selectJob(Job job) {
      return filter == null || filter.select(job);
   }
   
   /**
    * Stops the {@link Job} collection.
    */
   public void stop() {
      Job.getJobManager().removeJobChangeListener(listener);
   }

   /**
    * Returns the found {@link Job}s.
    * @return The found {@link Job}s.
    */
   public Job[] getJobs() {
      synchronized (jobs) {
         return jobs.toArray(new Job[jobs.size()]);
      }
   }

   /**
    * Removes all found {@link Job}s.
    */
   public void clearJobs() {
      synchronized (jobs) {
         jobs.clear();
      }
   }

   /**
    * Returns the optional {@link IFilter} to filter {@link Job}s added to {@link #getJobs()}.
    * @return The used {@link IFilter} or {@code null} if no {@link IFilter} is used.
    */
   public IFilter<Job> getFilter() {
      return filter;
   }

   /**
    * Sets the optional {@link IFilter} to filter {@link Job}s added to {@link #getJobs()}.
    * @param filter The {@link IFilter} to use or {@code null} if no {@link IFilter} should be used.
    */
   public void setFilter(IFilter<Job> filter) {
      this.filter = filter;
   }
}