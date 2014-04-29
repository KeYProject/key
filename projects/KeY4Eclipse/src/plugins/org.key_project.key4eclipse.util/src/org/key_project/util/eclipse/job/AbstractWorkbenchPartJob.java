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
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.util.eclipse.JobUtil;
import org.key_project.util.eclipse.job.ObjectchedulingRule;
import org.key_project.util.java.ObjectUtil;

/**
 * Abstract super class for {@link Job}s executed in an {@link IWorkbenchPart}
 * which have to be executed in serial order. 
 * @author Martin Hentschel
 */
public abstract class AbstractWorkbenchPartJob extends Job {
   /**
    * The {@link IWorkbenchPart} which has executed this {@link Job}.
    */
   private IWorkbenchPart part;
   
   /**
    * Constructor.
    * @param name The name of this {@link Job}.
    * @param part The {@link IWorkbenchPart} which has executed this {@link Job}.
    */
   public AbstractWorkbenchPartJob(String name, IWorkbenchPart part) {
      super(name);
      this.part = part;
      setRule(new ObjectchedulingRule(part));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean belongsTo(Object family) {
      if (ObjectUtil.equals(part, family)) {
         return true;
      }
      else {
         return super.belongsTo(family);
      }
   }
   
   /**
    * Cancels all {@link Job}s which does something with the given {@link IWorkbenchPart}.
    * @param part The {@link IWorkbenchPart} to cancel his {@link Job}s.
    * @return The canceled {@link Job}s.
    */
   public static Job[] cancelJobs(IWorkbenchPart part) {
      Job[] jobs = getJobs(part);
      JobUtil.cancel(jobs);
      return jobs;
   }
   
   /**
    * Returns all {@link Job}s that does something with the given {@link IWorkbenchPart}.
    * @param part The {@link IWorkbenchPart} to search {@link Job}s for.
    * @return The {@link Job}s that does something with the given {@link IWorkbenchPart}.
    */
   public static Job[] getJobs(IWorkbenchPart part) {
      return Job.getJobManager().find(part);
   }
}