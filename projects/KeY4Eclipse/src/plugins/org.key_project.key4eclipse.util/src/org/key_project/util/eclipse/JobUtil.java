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

package org.key_project.util.eclipse;

import org.eclipse.core.runtime.jobs.Job;

/**
 * Provides static utility methods for {@link Job}s.
 * @author Martin Hentschel
 */
public class JobUtil {
   /**
    * Forbid instances by this private constructor.
    */
   private JobUtil() {
   }
   
   /**
    * Cancels all given {@link Job}s.
    * @param jobs The {@link Job}s to cancel.
    */
   public static void cancel(Job[] jobs) {
      if (jobs != null) {
         for (Job job : jobs) {
            job.cancel();
         }
      }
   }

   /**
    * Blocks the current {@link Thread} until all given {@link Job}s 
    * have finished.
    * @param jobs The given {@link Job}s to wait for.
    * @param sleepTime The time to sleep before the next check is done.
    */
   public static void waitFor(Job[] jobs, int sleepTime) {
      if (jobs != null) {
         for (Job job : jobs) {
            waitFor(job, sleepTime);
         }
      }
   }

   /**
    * Blocks the current {@link Thread} until all given {@link Job}s 
    * have finished.
    * @param jobs The given {@link Job}s to wait for.
    * @param sleepTime The time to sleep before the next check is done.
    */
   public static void waitFor(Iterable<Job> jobs, int sleepTime) {
      if (jobs != null) {
         for (Job job : jobs) {
            waitFor(job, sleepTime);
         }
      }
   }

   /**
    * Blocks the current {@link Thread} until the given {@link Job} has finished.
    * @param job The {@link Job} to wait for.
    * @param sleepTime The time to sleep before the next check is done.
    */
   public static void waitFor(Job job, int sleepTime) {
      if (job != null) {
         while (job.getState() != Job.NONE) {
            try {
               Thread.sleep(sleepTime);
            }
            catch (InterruptedException e) {
               // Nothing to do.
            }
         }
      }
   }
}