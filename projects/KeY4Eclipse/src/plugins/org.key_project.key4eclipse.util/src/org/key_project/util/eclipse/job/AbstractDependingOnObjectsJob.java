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

import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.JobUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * Abstract super class for {@link Job}s depending on a single {@link Object}
 * and thus have to be executed in serial order. 
 * @author Martin Hentschel
 */
public abstract class AbstractDependingOnObjectsJob extends Job {
   /**
    * The {@link Object}s on which this {@link Job} depends on.
    */
   private final Object[] objects;
   
   /**
    * Constructor.
    * @param name The name of this {@link Job}.
    * @param objects The {@link Object}s on which this {@link Job} depends on.
    */
   public AbstractDependingOnObjectsJob(String name, Object... objects) {
      super(name);
      this.objects = objects;
      setRule(new ObjectsSchedulingRule(objects));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean belongsTo(Object family) {
      if (ArrayUtil.contains(objects, family)) {
         return true;
      }
      else {
         return super.belongsTo(family);
      }
   }
   
   /**
    * Cancels all {@link Job}s which does something with the given {@link Object}.
    * @param object The {@link Object} to cancel his {@link Job}s.
    * @return The canceled {@link Job}s.
    */
   public static Job[] cancelJobs(Object object) {
      Job[] jobs = getJobs(object);
      JobUtil.cancel(jobs);
      return jobs;
   }
   
   /**
    * Returns all {@link Job}s that does something with the given {@link Object}.
    * @param object The {@link Object} to search {@link Job}s for.
    * @return The {@link Job}s that does something with the given {@link Object}.
    */
   public static Job[] getJobs(Object object) {
      return Job.getJobManager().find(object);
   }
}